# $Id: CNCCanvas.py,v 1.7 2014/10/15 15:04:06 bnv Exp $
#
# Author:       vvlachoudis@gmail.com
# Date: 24-Aug-2014

import math
import time
import sys

from tkinter import (
    TclError,
    FALSE,
    N,
    S,
    W,
    E,
    NS,
    EW,
    NSEW,
    CENTER,
    NONE,
    BOTH,
    LEFT,
    RIGHT,
    RAISED,
    HORIZONTAL,
    VERTICAL,
    ALL,
    DISABLED,
    LAST,
    SCROLL,
    UNITS,
    StringVar,
    IntVar,
    BooleanVar,
    Button,
    Checkbutton,
    Frame,
    Label,
    Radiobutton,
    Scrollbar,
    OptionMenu,
)
import tkinter
from tkinter_gl import GLCanvas

from OpenGL.GL import *
from OpenGL.GLU import *


import bmath
import Camera
import tkExtra
import Utils
from CNC import CNC

# Probe mapping we need PIL and numpy
try:
    from PIL import Image, ImageTk
    import numpy

    # Resampling image based on PIL library and converting to RGB.
    # options possible: NEAREST, BILINEAR, BICUBIC, ANTIALIAS
    RESAMPLE = Image.NEAREST  # resize type
except Exception:
    from tkinter import Image
    numpy = None
    RESAMPLE = None

ANTIALIAS_CHEAP = False

VIEW_XY = 0
VIEW_XZ = 1
VIEW_YZ = 2
VIEW_ISO1 = 3
VIEW_ISO2 = 4
VIEW_ISO3 = 5
VIEWS = ["Perspective", "Orthographic"]
PROJECTION_PERSPECTIVE = 0
PROJECTION_ORTHOGRAPHIC = 1

INSERT_WIDTH2 = 3
GANTRY_R = 4
GANTRY_X = GANTRY_R * 2  # 10
GANTRY_Y = GANTRY_R  # 5
GANTRY_H = GANTRY_R * 5  # 20
DRAW_TIME = 5  # Maximum draw time permitted

INSERT_COLOR = "Blue"
GANTRY_COLOR = "Red"
MARGIN_COLOR = "Magenta"
GRID_COLOR = "Gray"
BOX_SELECT = "Cyan"
TAB_COLOR = "DarkOrange"
TABS_COLOR = "Orange"
WORK_COLOR = "Orange"
CAMERA_COLOR = "Cyan"
CANVAS_COLOR = "White"

ENABLE_COLOR = "Black"
DISABLE_COLOR = "LightGray"
SELECT_COLOR = "Blue"
SELECT2_COLOR = "DarkCyan"
PROCESS_COLOR = "Green"

MOVE_COLOR = "DarkCyan"
RULER_COLOR = "Green"
PROBE_TEXT_COLOR = "Green"

INFO_COLOR = "Gold"

SELECTION_TAGS = ("sel", "sel2", "sel3", "sel4")

ACTION_SELECT = 0
ACTION_SELECT_SINGLE = 1
ACTION_SELECT_AREA = 2
ACTION_SELECT_DOUBLE = 3

ACTION_PAN = 10
ACTION_ORIGIN = 11

ACTION_MOVE = 20
ACTION_ROTATE = 21
ACTION_GANTRY = 22
ACTION_WPOS = 23

ACTION_RULER = 30
ACTION_ADDORIENT = 31

SHIFT_MASK = 1
CONTROL_MASK = 4
ALT_MASK = 8
CONTROLSHIFT_MASK = SHIFT_MASK | CONTROL_MASK
CLOSE_DISTANCE = 5
MAXDIST = 10000
ZOOM = 1.25

S60 = math.sin(math.radians(60))
C60 = math.cos(math.radians(60))

DEF_CURSOR = ""
MOUSE_CURSOR = {
    ACTION_SELECT: DEF_CURSOR,
    ACTION_SELECT_AREA: "right_ptr",
    ACTION_PAN: "fleur",
    ACTION_ORIGIN: "cross",
    ACTION_MOVE: "hand1",
    ACTION_ROTATE: "exchange",
    ACTION_GANTRY: "target",
    ACTION_WPOS: "diamond_cross",
    ACTION_RULER: "tcross",
    ACTION_ADDORIENT: "tcross",
}


# -----------------------------------------------------------------------------
def mouseCursor(action):
    return MOUSE_CURSOR.get(action, DEF_CURSOR)


# =============================================================================
# Raise an alarm exception
# =============================================================================
class AlarmException(Exception):
    pass


# =============================================================================
# Drawing canvas
# =============================================================================
class CNCCanvas(GLCanvas):
    def __init__(self, master, app, *kw, **kwargs):
        GLCanvas.__init__(self, master, *kw, **kwargs)

        # Global variables
        self.projection = PROJECTION_PERSPECTIVE
        self.app = app
        self.cnc = app.cnc
        self.gcode = app.gcode
        self.actionVar = IntVar()
        self.r = [0,0,0]
        self.t = [0,0,0]
        self.scale = 1.0

        # Canvas binding
        self.bind("<Configure>", self.configureEvent)
        self.bind("<Motion>", self.motion)

        self.bind("<Button-1>", self.click)
        self.bind("<B1-Motion>", self.buttonMotion)
        self.bind("<ButtonRelease-1>", self.release)
        self.bind("<Double-1>", self.double)

        self.bind("<B2-Motion>", self.pan)
        self.bind("<ButtonRelease-2>", self.panRelease)
        self.bind("<Button-4>", self.mouseZoomIn)
        self.bind("<Button-5>", self.mouseZoomOut)
        self.bind("<MouseWheel>", self.wheel)

        self.bind("<Shift-Button-4>", self.panLeft)
        self.bind("<Shift-Button-5>", self.panRight)
        self.bind("<Control-Button-4>", self.panUp)
        self.bind("<Control-Button-5>", self.panDown)

        self.bind("<Control-Key-Left>", self.panLeft)
        self.bind("<Control-Key-Right>", self.panRight)
        self.bind("<Control-Key-Up>", self.panUp)
        self.bind("<Control-Key-Down>", self.panDown)

        self.bind("<Escape>", self.actionCancel)
        self.bind("<Key>", self.handleKey)

        self.bind("<Control-Key-S>", self.cameraSave)
        self.bind("<Control-Key-t>", self.__test)

        self.bind("<Control-Key-equal>", self.menuZoomIn)
        self.bind("<Control-Key-minus>", self.menuZoomOut)

        self.x0 = 0.0
        self.y0 = 0.0
        self.zoom = 1.0
        self.__tzoom = 1.0  # delayed zoom (temporary)
        self._items = {}

        self._x = self._y = 0
        self._xp = self._yp = 0
        self.action = ACTION_SELECT
        self._mouseAction = None
        self._inDraw = False  # semaphore for parsing
        self._gantry1 = None
        self._gantry2 = None
        self._select = None
        self._margin = None
        self._amargin = None
        self._workarea = None
        self._vector = None
        self._lastActive = None
        self._lastGantry = None

        self._probeImage = None
        self._probeTkImage = None
        self._probe = None

        self.camera = Camera.Camera("aligncam")
        self.cameraAnchor = CENTER  # Camera anchor location "" for gantry
        self.cameraRotation = 0.0  # camera Z angle
        self.cameraXCenter = 0.0  # camera X center offset
        self.cameraYCenter = 0.0  # camera Y center offset
        self.cameraScale = 10.0  # camera pixels/unit
        self.cameraEdge = False  # edge detection
        self.cameraR = 1.5875  # circle radius in units (mm/inched)
        self.cameraDx = 0  # camera shift vs gantry
        self.cameraDy = 0
        self.cameraZ = None  # if None it will not make any Z movement for the camera
        self.cameraSwitch = False  # Look at spindle(False) or camera(True)
        self._cameraAfter = None  # Camera anchor location "" for gantry
        self._cameraMaxWidth = 640  # on zoom over this size crop the image
        self._cameraMaxHeight = 480
        self._cameraImage = None
        self._cameraHori = None  # cross hair items
        self._cameraVert = None
        self._cameraCircle = None
        self._cameraCircle2 = None

        self.draw_axes = True  # Drawing flags
        self.draw_grid = True
        self.draw_margin = True
        self.draw_probe = True
        self.draw_workarea = True
        self.draw_paths = True
        self.draw_rapid = True  # draw rapid motions
        self._wx = self._wy = self._wz = 0.0  # work position
        self._dx = self._dy = self._dz = 0.0  # work-machine position

        self._vx0 = self._vy0 = self._vz0 = 0  # vector move coordinates
        self._vx1 = self._vy1 = self._vz1 = 0  # vector move coordinates

        self._orientSelected = None

        self.reset()
        self.initPosition()

    # ----------------------------------------------------------------------
    def reset(self):
        self.zoom = 1.0

    # ----------------------------------------------------------------------
    # Set status message
    # ----------------------------------------------------------------------
    def status(self, msg):
        self.event_generate("<<Status>>", data=msg)

    # ----------------------------------------------------------------------
    def setMouseStatus(self, event):
        data = "%.4f %.4f %.4f" % self.canvas2xyz(
            event.x, event.y
        )
        self.event_generate("<<Coords>>", data=data)

    # ----------------------------------------------------------------------
    def handleKey(self, event):
        if event.char == "a":
            self.event_generate("<<SelectAll>>")
        elif event.char == "A":
            self.event_generate("<<SelectNone>>")
        elif event.char == "e":
            self.event_generate("<<Expand>>")
        elif event.char == "f":
            self.fit2Screen()
        elif event.char == "g":
            self.setActionGantry()
        elif event.char == "l":
            self.event_generate("<<EnableToggle>>")
        elif event.char == "m":
            self.setActionMove()
        elif event.char == "n":
            self.event_generate("<<ShowInfo>>")
        elif event.char == "o":
            self.setActionOrigin()
        elif event.char == "r":
            self.setActionRuler()
        elif event.char == "s":
            self.setActionSelect()
        elif event.char == "x":
            self.setActionPan()
        elif event.char == "z":
            self.menuZoomIn()
        elif event.char == "Z":
            self.menuZoomOut()

    # ----------------------------------------------------------------------
    def setAction(self, action):
        self.action = action
        self.actionVar.set(action)
        self._mouseAction = None
        self.config(cursor=mouseCursor(self.action), background="White")

    # ----------------------------------------------------------------------
    def actionCancel(self, event=None):
        if self.action != ACTION_SELECT or (
            self._mouseAction != ACTION_SELECT and self._mouseAction is not None
        ):
            self.setAction(ACTION_SELECT)
            return "break"

    # ----------------------------------------------------------------------
    def setActionSelect(self, event=None):
        self.setAction(ACTION_SELECT)
        self.status(_("Select objects with mouse"))

    # ----------------------------------------------------------------------
    def setActionPan(self, event=None):
        self.setAction(ACTION_PAN)
        self.status(_("Pan viewport"))

    # ----------------------------------------------------------------------
    def setActionOrigin(self, event=None):
        self.setAction(ACTION_ORIGIN)
        self.status(_("Click to set the origin (zero)"))

    # ----------------------------------------------------------------------
    def setActionMove(self, event=None):
        self.setAction(ACTION_MOVE)
        self.status(_("Move graphically objects"))

    # ----------------------------------------------------------------------
    def setActionGantry(self, event=None):
        self.setAction(ACTION_GANTRY)
        self.config(background="seashell")
        self.status(_("Move CNC gantry to mouse location"))

    # ----------------------------------------------------------------------
    def setActionWPOS(self, event=None):
        self.setAction(ACTION_WPOS)
        self.config(background="ivory")
        self.status(
            _("Set mouse location as current machine position (X/Y only)"))

    # ----------------------------------------------------------------------
    def setActionRuler(self, event=None):
        self.setAction(ACTION_RULER)
        self.status(_("Drag a ruler to measure distances"))

    # ----------------------------------------------------------------------
    def setActionAddMarker(self, event=None):
        self.setAction(ACTION_ADDORIENT)
        self.status(_("Add an orientation marker"))

    # ----------------------------------------------------------------------
    # Convert canvas cx,cy coordinates to machine space
    # ----------------------------------------------------------------------
    def canvas2Machine(self, cx, cy):
        return self.canvas2xyz(cx,cy)

    # ----------------------------------------------------------------------
    # Image (pixel) coordinates to machine
    # ----------------------------------------------------------------------
    def image2Machine(self, x, y):
        return self.canvas2Machine(x, y)

    # ----------------------------------------------------------------------
    # Move gantry to mouse location
    # ----------------------------------------------------------------------
    def actionGantry(self, x, y):
        u, v, w = self.image2Machine(x, y)
        self.app.goto(u, v, w)
        self.setAction(ACTION_SELECT)

    # ----------------------------------------------------------------------
    # Set the work coordinates to mouse location
    # ----------------------------------------------------------------------
    def actionWPOS(self, x, y):
        u, v, w = self.image2Machine(x, y)
        self.app.mcontrol._wcsSet(u, v, w)
        self.setAction(ACTION_SELECT)

    # ----------------------------------------------------------------------
    # Add an orientation marker at mouse location
    # ----------------------------------------------------------------------
    def actionAddOrient(self, x, y):
        cx, cy = self.snapPoint(self.canvasx(x), self.canvasy(y))
        u, v, w = self.canvas2Machine(cx, cy)
        if u is None or v is None:
            self.status(
                _("ERROR: Cannot set X-Y marker  with the current view"))
            return
        self._orientSelected = len(self.gcode.orient)
        self.gcode.orient.add(CNC.vars["wx"], CNC.vars["wy"], u, v)
        self.event_generate("<<OrientSelect>>", data=self._orientSelected)
        self.setAction(ACTION_SELECT)

    # ----------------------------------------------------------------------
    # Find item selected
    # ----------------------------------------------------------------------
    def click(self, event):
        self.focus_set()
        self._x = self._xp = event.x
        self._y = self._yp = event.y

        if event.state & CONTROLSHIFT_MASK == CONTROLSHIFT_MASK:
            self.actionGantry(event.x, event.y)
            return

        elif self.action == ACTION_SELECT:
            self._mouseAction = ACTION_SELECT_SINGLE

        elif self.action in (ACTION_MOVE, ACTION_RULER):
            i = self.canvasx(event.x)
            j = self.canvasy(event.y)
            if self.action == ACTION_RULER and self._vector is not None:
                # Check if we hit the existing ruler
                coords = self.coords(self._vector)
                if abs(coords[0] - i) <= CLOSE_DISTANCE and abs(
                    coords[1] - j <= CLOSE_DISTANCE
                ):
                    # swap coordinates
                    coords[0], coords[2] = coords[2], coords[0]
                    coords[1], coords[3] = coords[3], coords[1]
                    self.coords(self._vector, *coords)
                    self._vx0, self._vy0, self._vz0 = self.canvas2xyz(
                        coords[0], coords[1]
                    )
                    self._mouseAction = self.action
                    return
                elif abs(coords[2] - i) <= CLOSE_DISTANCE and abs(
                    coords[3] - j <= CLOSE_DISTANCE
                ):
                    self._mouseAction = self.action
                    return

            if self._vector:
                self.delete(self._vector)
            if self.action == ACTION_MOVE:
                # Check if we clicked on a selected item
                try:
                    for item in self.find_overlapping(
                        i - CLOSE_DISTANCE,
                        j - CLOSE_DISTANCE,
                        i + CLOSE_DISTANCE,
                        j + CLOSE_DISTANCE,
                    ):
                        tags = self.gettags(item)
                        if (
                            "sel" in tags
                            or "sel2" in tags
                            or "sel3" in tags
                            or "sel4" in tags
                        ):
                            break
                    else:
                        self._mouseAction = ACTION_SELECT_SINGLE
                        return
                    fill = MOVE_COLOR
                    arrow = LAST
                except Exception:
                    self._mouseAction = ACTION_SELECT_SINGLE
                    return
            else:
                fill = RULER_COLOR
                arrow = BOTH
            self._vector = self.create_line(
                (i, j, i, j), fill=fill, arrow=arrow)
            self._vx0, self._vy0, self._vz0 = self.canvas2xyz(i, j)
            self._mouseAction = self.action

        # Move gantry to position
        elif self.action == ACTION_GANTRY:
            self.actionGantry(event.x, event.y)

        # Move gantry to position
        elif self.action == ACTION_WPOS:
            self.actionWPOS(event.x, event.y)

        # Add orientation marker
        elif self.action == ACTION_ADDORIENT:
            self.actionAddOrient(event.x, event.y)

        # Set coordinate origin
        elif self.action == ACTION_ORIGIN:
            i = self.canvasx(event.x)
            j = self.canvasy(event.y)
            x, y, z = self.canvas2xyz(i, j)
            self.app.insertCommand(_("origin {:g} {:g} {:g}").format(x, y, z),
                                   True)
            self.setActionSelect()

        elif self.action == ACTION_PAN:
            self.pan(event)

    # ----------------------------------------------------------------------
    # Canvas motion button 1
    # ----------------------------------------------------------------------
    def buttonMotion(self, event):
        dx = event.x - self._x
        dy = event.y - self._y
        if self.action == ACTION_SELECT:
                self.r[0] += dy
                self.r[1] += dx
        elif self.action == ACTION_PAN:
                self.t[0] += dx*0.1
                self.t[1] -= dy*0.1

        self._x = event.x
        self._y = event.y
        self.draw()
        self.setMouseStatus(event)

    # ----------------------------------------------------------------------
    # Canvas release button1. Select area
    # ----------------------------------------------------------------------
    def release(self, event):
        if self._mouseAction in (
            ACTION_SELECT_SINGLE,
            ACTION_SELECT_DOUBLE,
            ACTION_SELECT_AREA,
        ):
            x,y,z = self.canvas2xyz(event.x, event.y)
            print(f"Clicked at: {x}, {y}, {z}")
            self._mouseAction = None

        elif self._mouseAction == ACTION_MOVE:
            i = event.x
            j = event.y
            self._vx1, self._vy1, self._vz1 = self.canvas2xyz(i, j)
            dx = self._vx1 - self._vx0
            dy = self._vy1 - self._vy0
            dz = self._vz1 - self._vz0
            self.status(_("Move by {:g}, {:g}, {:g}").format(dx, dy, dz))
            self.app.insertCommand(("move %g %g %g") % (dx, dy, dz), True)

        elif self.action == ACTION_PAN:
            self.action = ACTION_SELECT
            self.config(cursor=mouseCursor(self.action))

        self.draw()

    # ----------------------------------------------------------------------
    def double(self, event):
        self._mouseAction = ACTION_SELECT_DOUBLE

    # ----------------------------------------------------------------------
    def motion(self, event):
        self.setMouseStatus(event)

    # -----------------------------------------------------------------------
    # Testing routine
    # -----------------------------------------------------------------------
    def __test(self, event):
        i = self.canvasx(event.x)
        j = self.canvasy(event.y)
        x, y, z = self.canvas2xyz(i, j)

    # ----------------------------------------------------------------------
    # Snap to the closest point if any
    # ----------------------------------------------------------------------
    def snapPoint(self, cx, cy):
        xs, ys = None, None
        if CNC.inch:
            dmin = (self.zoom / 25.4) ** 2  # 1mm maximum distance ...
        else:
            dmin = (self.zoom) ** 2
        dmin = (CLOSE_DISTANCE * self.zoom) ** 2

        # ... and if we are closer than 5pixels
        for item in self.find_closest(cx, cy, CLOSE_DISTANCE):
            try:
                bid, lid = self._items[item]
            except KeyError:
                continue

            # Very cheap and inaccurate approach :)
            coords = self.coords(item)
            x = coords[0]  # first
            y = coords[1]  # point
            d = (cx - x) ** 2 + (cy - y) ** 2
            if d < dmin:
                dmin = d
                xs, ys = x, y

            x = coords[-2]  # last
            y = coords[-1]  # point
            d = (cx - x) ** 2 + (cy - y) ** 2
            if d < dmin:
                dmin = d
                xs, ys = x, y

            # I need to check the real code and if
            # an arc check also the center?

        if xs is not None:
            return xs, ys
        else:
            return cx, cy

    # ----------------------------------------------------------------------
    # Get margins of selected items
    # ----------------------------------------------------------------------
    def getMargins(self):
        return 0,0

    # ----------------------------------------------------------------------
    def configureEvent(self, event):
        self.cameraPosition()

    # ----------------------------------------------------------------------
    def pan(self, event):
        self._x = event.x
        self._y = event.y
        self.config(cursor=mouseCursor(ACTION_PAN))
        self.action = ACTION_PAN

    # ----------------------------------------------------------------------
    def panRelease(self, event):
        self._mouseAction = None
        self.config(cursor=mouseCursor(self.action))

    # ----------------------------------------------------------------------
    def panLeft(self, event=None):
        pass

    def panRight(self, event=None):
        pass

    def panUp(self, event=None):
        pass

    def panDown(self, event=None):
        pass

    # ----------------------------------------------------------------------
    # Delay zooming to cascade multiple zoom actions
    # ----------------------------------------------------------------------
    def zoomCanvas(self, x, y, zoom):
        self.scale *= zoom
        self.draw()

    # ----------------------------------------------------------------------
    # Return selected objects bounding box
    # ----------------------------------------------------------------------
    def selBbox(self):
        return None

    # ----------------------------------------------------------------------
    # Zoom to Fit to Screen
    # ----------------------------------------------------------------------
    def fit2Screen(self, event=None):
        """Zoom to Fit to Screen"""
        if self.gcode.is_empty():
            return
        xmin, xmax, ymin, ymax, zmin, zmax = self.gcode.get_max_min_coords()

        # Center the view
        self.t[0] = -(xmin + xmax) / 2
        self.t[1] = -(ymin + ymax) / 2

        # Zoom to fit
        w = xmax - xmin
        h = ymax - ymin

        if self.winfo_width() > self.winfo_height():
            self.scale = self.winfo_height() / h * 0.5
        else:
            self.scale = self.winfo_width() / w * 0.5
        self.draw()

    # ----------------------------------------------------------------------
    def menuZoomIn(self, event=None):
        x = int(self.cget("width")) // 2
        y = int(self.cget("height")) // 2
        self.zoomCanvas(x, y, 2.0)

    # ----------------------------------------------------------------------
    def menuZoomOut(self, event=None):
        x = int(self.cget("width")) // 2
        y = int(self.cget("height")) // 2
        self.zoomCanvas(x, y, 0.5)

    # ----------------------------------------------------------------------
    def mouseZoomIn(self, event):
        self.zoomCanvas(event.x, event.y, ZOOM)

    # ----------------------------------------------------------------------
    def mouseZoomOut(self, event):
        self.zoomCanvas(event.x, event.y, 1.0 / ZOOM)

    # ----------------------------------------------------------------------
    def wheel(self, event):
        self.zoomCanvas(event.x, event.y, pow(ZOOM, (event.delta // 120)))

    # ----------------------------------------------------------------------
    # Change the insert marker location
    # ----------------------------------------------------------------------
    def activeMarker(self, item):
        if item is None:
            return
        b, i = item
        if i is None:
            return
        block = self.gcode[b]
        item = block.path(i)

        if item is not None and item != self._lastActive:
            if self._lastActive is not None:
                self.itemconfig(self._lastActive, arrow=NONE)
            self._lastActive = item
            self.itemconfig(self._lastActive, arrow=LAST)

    # ----------------------------------------------------------------------
    # Display gantry
    # ----------------------------------------------------------------------
    def gantry(self, wx, wy, wz, mx, my, mz):
        self._lastGantry = (wx, wy, wz)
        self._drawGantry(wx, wy, wz)
        if self._cameraImage and self.cameraAnchor == NONE:
            self.cameraPosition()

        dx = wx - mx
        dy = wy - my
        dz = wz - mz
        if (
            abs(dx - self._dx) > 0.0001
            or abs(dy - self._dy) > 0.0001
            or abs(dz - self._dz) > 0.0001
        ):
            self._dx = dx
            self._dy = dy
            self._dz = dz

            if not self.draw_workarea:
                return
            xmin = self._dx - CNC.travel_x
            ymin = self._dy - CNC.travel_y
            xmax = self._dx
            ymax = self._dy

            xyz = [
                (xmin, ymin, 0.0),
                (xmax, ymin, 0.0),
                (xmax, ymax, 0.0),
                (xmin, ymax, 0.0),
                (xmin, ymin, 0.0),
            ]
            #FIXME
            #coords = []
            #for x, y in self.plotCoords(xyz):
            #    coords.append(x)
            #    coords.append(y)
            #self.coords(self._workarea, *coords)

    # ----------------------------------------------------------------------
    # Clear highlight of selection
    # ----------------------------------------------------------------------
    def clearSelection(self):
        if self._lastActive is not None:
            self.itemconfig(self._lastActive, arrow=NONE)
            self._lastActive = None

        for i in self.find_withtag("sel"):
            bid, lid = self._items[i]
            if bid:
                try:
                    block = self.gcode[bid]
                    if block.color:
                        fill = block.color
                    else:
                        fill = ENABLE_COLOR
                except IndexError:
                    fill = ENABLE_COLOR
            else:
                fill = ENABLE_COLOR
            self.itemconfig(i, width=1, fill=fill)

        self.itemconfig("sel2", width=1, fill=DISABLE_COLOR)
        self.itemconfig("sel3", width=1, fill=TAB_COLOR)
        self.itemconfig("sel4", width=1, fill=DISABLE_COLOR)
        for i in SELECTION_TAGS:
            self.dtag(i)
        self.delete("info")

    # ----------------------------------------------------------------------
    # Highlight selected items
    # ----------------------------------------------------------------------
    def select(self, items):
        for b, i in items:
            block = self.gcode[b]
            if i is None:
                sel = block.enable and "sel" or "sel2"
                for path in block._path:
                    if path is not None:
                        self.addtag_withtag(sel, path)
                sel = block.enable and "sel3" or "sel4"

            elif isinstance(i, int):
                path = block.path(i)
                if path:
                    sel = block.enable and "sel" or "sel2"
                    self.addtag_withtag(sel, path)

        self.itemconfig("sel", width=2, fill=SELECT_COLOR)
        self.itemconfig("sel2", width=2, fill=SELECT2_COLOR)
        self.itemconfig("sel3", width=2, fill=TAB_COLOR)
        self.itemconfig("sel4", width=2, fill=TABS_COLOR)
        for i in SELECTION_TAGS:
            self.tag_raise(i)
        self.drawMargin()

    # ----------------------------------------------------------------------
    # Select orientation marker
    # ----------------------------------------------------------------------
    def selectMarker(self, item):
        # find marker
        for i, paths in enumerate(self.gcode.orient.paths):
            if item in paths:
                self._orientSelected = i
                for j in paths:
                    self.itemconfig(j, width=2)
                self.event_generate("<<OrientSelect>>", data=i)
                return
        self._orientSelected = None

    # ----------------------------------------------------------------------
    # Highlight marker that was selected
    # ----------------------------------------------------------------------
    def orientChange(self, marker):
        self.itemconfig("Orient", width=1)
        if marker >= 0:
            self._orientSelected = marker
            try:
                for i in self.gcode.orient.paths[self._orientSelected]:
                    self.itemconfig(i, width=2)
            except IndexError:
                self.drawOrient()
        else:
            self._orientSelected = None

    # ----------------------------------------------------------------------
    # Display graphical information on selected blocks
    # ----------------------------------------------------------------------
    def showInfo(self, blocks):
        #FIXME
        pass

    # -----------------------------------------------------------------------
    def cameraOn(self, event=None):
        if not self.camera.start():
            return
        self.cameraRefresh()

    # -----------------------------------------------------------------------
    def cameraOff(self, event=None):
        self.delete(self._cameraImage)
        self.delete(self._cameraHori)
        self.delete(self._cameraVert)
        self.delete(self._cameraCircle)
        self.delete(self._cameraCircle2)

        self._cameraImage = None
        if self._cameraAfter:
            self.after_cancel(self._cameraAfter)
            self._cameraAfter = None
        self.camera.stop()

    # -----------------------------------------------------------------------
    def cameraUpdate(self):
        if not self.camera.isOn():
            return
        if self._cameraAfter:
            self.after_cancel(self._cameraAfter)
            self._cameraAfter = None
        self.cameraRefresh()
        self.cameraPosition()

    # -----------------------------------------------------------------------
    def cameraRefresh(self):
        if not self.camera.read():
            self.cameraOff()
            return
        self.camera.rotation = self.cameraRotation
        self.camera.xcenter = self.cameraXCenter
        self.camera.ycenter = self.cameraYCenter
        if self.cameraEdge:
            self.camera.canny(50, 200)
        if self.cameraAnchor == NONE or self.zoom / self.cameraScale > 1.0:
            self.camera.resize(
                self.zoom / self.cameraScale,
                self._cameraMaxWidth,
                self._cameraMaxHeight,
            )
        if self._cameraImage is None:
            self._cameraImage = self.create_image((0, 0), tag="CameraImage")
            self.lower(self._cameraImage)
            # create cross hair at dummy location we will correct latter
            self._cameraHori = self.create_line(
                0, 0, 1, 0, fill=CAMERA_COLOR, tag="CrossHair"
            )
            self._cameraVert = self.create_line(
                0, 0, 0, 1, fill=CAMERA_COLOR, tag="CrossHair"
            )
            self._cameraCircle = self.create_oval(
                0, 0, 1, 1, outline=CAMERA_COLOR, tag="CrossHair"
            )
            self._cameraCircle2 = self.create_oval(
                0, 0, 1, 1, outline=CAMERA_COLOR, dash=(3, 3), tag="CrossHair"
            )
            self.cameraPosition()
        try:
            self.itemconfig(self._cameraImage, image=self.camera.toTk())
        except Exception:
            pass
        self._cameraAfter = self.after(100, self.cameraRefresh)

    # -----------------------------------------------------------------------
    def cameraFreeze(self, freeze):
        if self.camera.isOn():
            self.camera.freeze(freeze)

    # -----------------------------------------------------------------------
    def cameraSave(self, event=None):
        try:
            self._count += 1
        except Exception:
            self._count = 1
        self.camera.save("camera%02d.png" % (self._count))

    # ----------------------------------------------------------------------
    # Reposition camera and crosshair
    # ----------------------------------------------------------------------
    def cameraPosition(self):
        if self._cameraImage is None:
            return
        w = self.winfo_width()
        h = self.winfo_height()
        hc, wc = self.camera.image.shape[:2]
        wc //= 2
        hc //= 2
        x = w // 2  # everything on center
        y = h // 2
        if self.cameraAnchor is NONE:
            if self._lastGantry is not None:
                x, y = self.plotCoords([self._lastGantry])[0]
            else:
                x = y = 0
            if not self.cameraSwitch:
                x += self.cameraDx * self.zoom
                y -= self.cameraDy * self.zoom
            r = self.cameraR * self.zoom
        else:
            if self.cameraAnchor != CENTER:
                if N in self.cameraAnchor:
                    y = hc
                elif S in self.cameraAnchor:
                    y = h - hc
                if W in self.cameraAnchor:
                    x = wc
                elif E in self.cameraAnchor:
                    x = w - wc
            x = self.canvasx(x)
            y = self.canvasy(y)
            if self.zoom / self.cameraScale > 1.0:
                r = self.cameraR * self.zoom
            else:
                r = self.cameraR * self.cameraScale

        self.coords(self._cameraImage, x, y)
        self.coords(self._cameraHori, x - wc, y, x + wc, y)
        self.coords(self._cameraVert, x, y - hc, x, y + hc)
        self.coords(self._cameraCircle, x - r, y - r, x + r, y + r)
        self.coords(
            self._cameraCircle2, x - r * 2, y - r * 2, x + r * 2, y + r * 2)

    # ----------------------------------------------------------------------
    # Crop center of camera and search it in subsequent movements
    # ----------------------------------------------------------------------
    def cameraMakeTemplate(self, r):
        if self._cameraImage is None:
            return
        self._template = self.camera.getCenterTemplate(r)

    # ----------------------------------------------------------------------
    def cameraMatchTemplate(self):
        return self.camera.matchTemplate(self._template)

    def init_opengl(self):
        """Initialise the GL canvas"""
        glEnable(GL_DEPTH_TEST)
        glEnable(GL_BLEND)
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
        glEnable(GL_LINE_SMOOTH)
        glHint(GL_LINE_SMOOTH_HINT, GL_NICEST)

        self.set_projection()
        self.set_modelview()

    def set_projection(self,):
        """Setup the projection matrix"""
        glMatrixMode(GL_PROJECTION)
        glLoadIdentity()
        if self.projection == PROJECTION_PERSPECTIVE:
            gluPerspective(45, self.winfo_width()/self.winfo_height(), 0.1, 1000.0)
        else:
            glOrtho(-100, 100, -100, 100, -100, 100)

    def set_modelview(self,):
        """Setup the modelview matrix"""
        glMatrixMode(GL_MODELVIEW)
        glLoadIdentity()
        glTranslatef(self.t[0], self.t[1], self.t[2]-400)
        glRotatef(self.r[0], 1, 0, 0)
        glRotatef(self.r[1], 0, 1, 0)
        glRotatef(self.r[2], 0, 0, 1)
        glScalef(self.scale, self.scale, self.scale)

    # ----------------------------------------------------------------------
    # Parse and draw the file from the editor to g-code commands
    # ----------------------------------------------------------------------
    def draw(self, view=None):
        if self._inDraw:
            return
        self._inDraw = True

        if view is not None:
            self.projection = view

        self.tkMakeCurrent()
        self.init_opengl()
        glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT)

        self.drawPaths()
        self.drawGrid()
        self.drawMargin()
        self.drawWorkarea()
        self.drawProbe()
        self.drawOrient()
        self.drawAxes()
        self.tkSwapBuffers()

        self._inDraw = False

    # ----------------------------------------------------------------------
    # Initialize gantry position
    # ----------------------------------------------------------------------
    def initPosition(self):
        self._cameraImage = None

        self._lastInsert = None
        self._lastActive = None
        self._select = None
        self._vector = None
        self._items.clear()
        self.cnc.initPath()
        self.cnc.resetAllMargins()

    # ----------------------------------------------------------------------
    # Draw gantry location
    # ----------------------------------------------------------------------
    def _drawGantry(self, x, y, z):
        glColor3f(1.0, 0.0, 0.0)
        glLineWidth(1.0)
        glBegin(GL_LINES)
        glVertex3f(x - 10, y, z)
        glVertex3f(x + 10, y, z)
        glVertex3f(x, y - 10, z)
        glVertex3f(x, y + 10, z)
        glVertex3f(x, y, z - 10)
        glVertex3f(x, y, z + 10)
        glEnd()

        glBegin(GL_LINE_LOOP)
        for i in range(360):
            rad = math.radians(i)
            glVertex3f(x + math.cos(rad) * 5, y + math.sin(rad) * 5, z)
        glEnd()

    # ----------------------------------------------------------------------
    # Draw system axes
    # ----------------------------------------------------------------------
    def drawAxes(self):
        if not self.draw_axes:
            return
        glLineWidth(1.0)
        glBegin(GL_LINES)
        # X-axis (red)
        glColor3f(1.0, 0.0, 0.0)
        glVertex3f(0.0, 0.0, 0.0)
        glVertex3f(10.0, 0.0, 0.0)
        # Y-axis (green)
        glColor3f(0.0, 1.0, 0.0)
        glVertex3f(0.0, 0.0, 0.0)
        glVertex3f(0.0, 10.0, 0.0)
        # Z-axis (blue)
        glColor3f(0.0, 0.0, 1.0)
        glVertex3f(0.0, 0.0, 0.0)
        glVertex3f(0.0, 0.0, 10.0)
        glEnd()


    # ----------------------------------------------------------------------
    # Draw margins of selected blocks
    # ----------------------------------------------------------------------
    def drawMargin(self):
        if not self.draw_margin:
            return

        if CNC.isMarginValid():
            glColor3f(1.0, 0.0, 1.0)
            glBegin(GL_LINE_LOOP)
            glVertex3f(CNC.vars["xmin"], CNC.vars["ymin"], 0.0)
            glVertex3f(CNC.vars["xmax"], CNC.vars["ymin"], 0.0)
            glVertex3f(CNC.vars["xmax"], CNC.vars["ymax"], 0.0)
            glVertex3f(CNC.vars["xmin"], CNC.vars["ymax"], 0.0)
            glEnd()

        if CNC.isAllMarginValid():
            glColor3f(1.0, 0.0, 1.0)
            glLineStipple(1, 0x3333)
            glEnable(GL_LINE_STIPPLE)
            glBegin(GL_LINE_LOOP)
            glVertex3f(CNC.vars["axmin"], CNC.vars["aymin"], 0.0)
            glVertex3f(CNC.vars["axmax"], CNC.vars["aymin"], 0.0)
            glVertex3f(CNC.vars["axmax"], CNC.vars["aymax"], 0.0)
            glVertex3f(CNC.vars["axmin"], CNC.vars["aymax"], 0.0)
            glEnd()
            glDisable(GL_LINE_STIPPLE)


    # ----------------------------------------------------------------------
    # Draw a workspace rectangle
    # ----------------------------------------------------------------------
    def drawWorkarea(self):
        if not self.draw_workarea:
            return
        xmin = self._dx - CNC.travel_x
        ymin = self._dy - CNC.travel_y
        xmax = self._dx
        ymax = self._dy

        glColor3f(1.0, 0.5, 0.0)
        glLineStipple(1, 0x3333)
        glEnable(GL_LINE_STIPPLE)
        glBegin(GL_LINE_LOOP)
        glVertex3f(xmin, ymin, 0.0)
        glVertex3f(xmax, ymin, 0.0)
        glVertex3f(xmax, ymax, 0.0)
        glVertex3f(xmin, ymax, 0.0)
        glEnd()
        glDisable(GL_LINE_STIPPLE)

    # ----------------------------------------------------------------------
    # Draw coordinates grid
    # ----------------------------------------------------------------------
    def drawGrid(self):
        if not self.draw_grid:
            return
        glLineWidth(1.0)
        glColor3f(0.5, 0.5, 0.5)
        glBegin(GL_LINES)
        for i in range(-100, 101, 10):
            glVertex3f(i, -100.0, 0.0)
            glVertex3f(i, 100.0, 0.0)
            glVertex3f(-100.0, i, 0.0)
            glVertex3f(100.0, i, 0.0)
        glEnd()

    # ----------------------------------------------------------------------
    # Display orientation markers
    # ----------------------------------------------------------------------
    def drawOrient(self, event=None):
        if not self.gcode.orient.markers:
            return

        w = 0.1 if CNC.inch else 2.5

        for i, (xm, ym, x, y) in enumerate(self.gcode.orient.markers):
            # Machine position (cross)
            glColor3f(0.0, 1.0, 0.0)
            glBegin(GL_LINES)
            glVertex3f(xm - w, ym, 0.0)
            glVertex3f(xm + w, ym, 0.0)
            glVertex3f(xm, ym - w, 0.0)
            glVertex3f(xm, ym + w, 0.0)
            glEnd()

            # GCode position (cross)
            glColor3f(1.0, 0.0, 0.0)
            glBegin(GL_LINES)
            glVertex3f(x - w, y, 0.0)
            glVertex3f(x + w, y, 0.0)
            glVertex3f(x, y - w, 0.0)
            glVertex3f(x, y + w, 0.0)
            glEnd()

            # Connecting line
            glColor3f(0.0, 0.0, 1.0)
            glLineStipple(1, 0x3333)
            glEnable(GL_LINE_STIPPLE)
            glBegin(GL_LINES)
            glVertex3f(xm, ym, 0.0)
            glVertex3f(x, y, 0.0)
            glEnd()
            glDisable(GL_LINE_STIPPLE)


    # ----------------------------------------------------------------------
    # Display probe
    # ----------------------------------------------------------------------
    def drawProbe(self):
        if not self.draw_probe:
            return
        if self.gcode.probe.isEmpty():
            return

        probe = self.gcode.probe

        # Draw probe grid
        glColor3f(1.0, 1.0, 0.0)
        glBegin(GL_LINES)
        for x in bmath.frange(probe.xmin, probe.xmax + 0.00001, probe.xstep()):
            glVertex3f(x, probe.ymin, 0.0)
            glVertex3f(x, probe.ymax, 0.0)
        for y in bmath.frange(probe.ymin, probe.ymax + 0.00001, probe.ystep()):
            glVertex3f(probe.xmin, y, 0.0)
            glVertex3f(probe.xmax, y, 0.0)
        glEnd()

        # Draw probe points
        glColor3f(0.0, 1.0, 0.0)
        glPointSize(5.0)
        glBegin(GL_POINTS)
        for x, y, z in probe.points:
            glVertex3f(x, y, z)
        glEnd()

    # ----------------------------------------------------------------------
    # Create the tkimage for the current projection
    # ----------------------------------------------------------------------
    def _projectProbeImage(self):
        #FIXME
        return 0,0

    # ----------------------------------------------------------------------
    # Draw the paths for the whole gcode file
    # ----------------------------------------------------------------------
    def drawPaths(self):
        if not self.draw_paths:
            for block in self.gcode.blocks:
                block.resetPath()
            return
        try:
            n = 1
            startTime = before = time.time()
            self.cnc.resetAllMargins()
            drawG = self.draw_rapid or self.draw_paths or self.draw_margin
            for i, block in enumerate(self.gcode.blocks):
                start = True  # start location found
                block.resetPath()

                # Draw block
                for j, line in enumerate(block):
                    n -= 1
                    if n == 0:
                        if time.time() - startTime > DRAW_TIME:
                            raise AlarmException()
                        # Force a periodic update since this loop can take time
                        if time.time() - before > 1.0:
                            self.update()
                            before = time.time()
                        n = 1000
                    try:
                        cmd = self.gcode.evaluate(
                            CNC.compileLine(line), self.app)
                        if isinstance(cmd, tuple):
                            cmd = None
                        else:
                            cmd = CNC.breakLine(cmd)
                    except AlarmException:
                        raise
                    except Exception:
                        sys.stderr.write(
                            _(">>> ERROR: {}\n").format(str(sys.exc_info()[1]))
                        )
                        sys.stderr.write(_("     line: {}\n").format(line))
                        cmd = None
                    if cmd is None or not drawG:
                        block.addPath(None)
                    else:
                        path = self.drawPath(block, cmd)
                        #self._items[path] = i, j
                        block.addPath(path)
                        if start and self.cnc.gcode in (1, 2, 3):
                            # Mark as start the first non-rapid motion
                            block.startPath(self.cnc.x, self.cnc.y, self.cnc.z)
                            start = False
                block.endPath(self.cnc.x, self.cnc.y, self.cnc.z)
        except AlarmException:
            self.status("Rendering takes TOO Long. Interrupted...")

    # ----------------------------------------------------------------------
    # Create path for one g command
    # ----------------------------------------------------------------------
    def drawPath(self, block, cmds):
        self.cnc.motionStart(cmds)
        xyz = self.cnc.motionPath()
        self.cnc.motionEnd()
        if xyz:
            self.cnc.pathLength(block, xyz)
            if self.cnc.gcode in (1, 2, 3):
                block.pathMargins(xyz)
                self.cnc.pathMargins(block)
            if block.enable:
                if self.cnc.gcode == 0 and self.draw_rapid:
                    xyz[0] = self._last
                self._last = xyz[-1]
            else:
                if self.cnc.gcode == 0:
                    return None

            if self.cnc.gcode == 0:
                if self.draw_rapid:
                    glColor3f(0.5, 0.5, 0.5)
                    glLineStipple(1, 0x3333)
                    glEnable(GL_LINE_STIPPLE)
            elif self.draw_paths:
                    glColor3f(0.0, 0.0, 0.0)
                    glDisable(GL_LINE_STIPPLE)

            glBegin(GL_LINE_STRIP)
            for x,y,z in xyz:
                glVertex3f(x,y,z)
            glEnd()
            glDisable(GL_LINE_STIPPLE)

        return None


    # ----------------------------------------------------------------------
    # Canvas to real coordinates
    # ----------------------------------------------------------------------
    def canvas2xyz(self, i, j):
        modelview = glGetDoublev(GL_MODELVIEW_MATRIX)
        projection = glGetDoublev(GL_PROJECTION_MATRIX)
        viewport = glGetIntegerv(GL_VIEWPORT)
        winX = float(i)
        winY = float(viewport[3] - float(j))
        winZ = glReadPixels(winX, winY, 1, 1, GL_DEPTH_COMPONENT, GL_FLOAT)
        x,y,z = gluUnProject(winX, winY, winZ, modelview, projection, viewport)
        return x,y,z


# =============================================================================
# Canvas Frame with toolbar
# =============================================================================
class CanvasFrame(Frame):
    def __init__(self, master, app, *kw, **kwargs):
        Frame.__init__(self, master, *kw, **kwargs)
        self.app = app

        self.draw_axes = BooleanVar()
        self.draw_grid = BooleanVar()
        self.draw_margin = BooleanVar()
        self.draw_probe = BooleanVar()
        self.draw_paths = BooleanVar()
        self.draw_rapid = BooleanVar()
        self.draw_workarea = BooleanVar()
        self.draw_camera = BooleanVar()
        self.view = StringVar()

        self.loadConfig()

        self.view.trace("w", self.viewChange)

        toolbar = Frame(self, relief=RAISED)
        toolbar.grid(row=0, column=0, columnspan=2, sticky=EW)

        self.canvas = CNCCanvas(self, app, background="White")
        # OpenGL context
        self.canvas.grid(row=1, column=0, sticky=NSEW)

        self.createCanvasToolbar(toolbar)

        self.grid_rowconfigure(1, weight=1)
        self.grid_columnconfigure(0, weight=1)

    # ----------------------------------------------------------------------
    def addWidget(self, widget):
        self.app.widgets.append(widget)

    # ----------------------------------------------------------------------
    def loadConfig(self):
        global INSERT_COLOR, GANTRY_COLOR, MARGIN_COLOR, GRID_COLOR
        global BOX_SELECT, ENABLE_COLOR, DISABLE_COLOR, SELECT_COLOR
        global SELECT2_COLOR, PROCESS_COLOR, MOVE_COLOR, RULER_COLOR
        global CAMERA_COLOR, PROBE_TEXT_COLOR, CANVAS_COLOR
        global DRAW_TIME

        self.draw_axes.set(bool(int(Utils.getBool("Canvas", "axes", True))))
        self.draw_grid.set(bool(int(Utils.getBool("Canvas", "grid", True))))
        self.draw_margin.set(bool(int(Utils.getBool("Canvas", "margin", True))))
        self.draw_paths.set(bool(int(Utils.getBool("Canvas", "paths", True))))
        self.draw_rapid.set(bool(int(Utils.getBool("Canvas", "rapid", True))))
        self.draw_workarea.set(
            bool(int(Utils.getBool("Canvas", "workarea", True))))

        self.view.set(Utils.getStr("Canvas", "view", VIEWS[0]))

        DRAW_TIME = Utils.getInt("Canvas", "drawtime", DRAW_TIME)

        INSERT_COLOR = Utils.getStr("Color", "canvas.insert", INSERT_COLOR)
        GANTRY_COLOR = Utils.getStr("Color", "canvas.gantry", GANTRY_COLOR)
        MARGIN_COLOR = Utils.getStr("Color", "canvas.margin", MARGIN_COLOR)
        GRID_COLOR = Utils.getStr("Color", "canvas.grid", GRID_COLOR)
        BOX_SELECT = Utils.getStr("Color", "canvas.selectbox", BOX_SELECT)
        ENABLE_COLOR = Utils.getStr("Color", "canvas.enable", ENABLE_COLOR)
        DISABLE_COLOR = Utils.getStr("Color", "canvas.disable", DISABLE_COLOR)
        SELECT_COLOR = Utils.getStr("Color", "canvas.select", SELECT_COLOR)
        SELECT2_COLOR = Utils.getStr("Color", "canvas.select2", SELECT2_COLOR)
        PROCESS_COLOR = Utils.getStr("Color", "canvas.process", PROCESS_COLOR)
        MOVE_COLOR = Utils.getStr("Color", "canvas.move", MOVE_COLOR)
        RULER_COLOR = Utils.getStr("Color", "canvas.ruler", RULER_COLOR)
        CAMERA_COLOR = Utils.getStr("Color", "canvas.camera", CAMERA_COLOR)
        PROBE_TEXT_COLOR = Utils.getStr(
            "Color", "canvas.probetext", PROBE_TEXT_COLOR)
        CANVAS_COLOR = Utils.getStr("Color", "canvas.background", CANVAS_COLOR)

    # ----------------------------------------------------------------------
    def saveConfig(self):
        Utils.setInt("Canvas", "drawtime", DRAW_TIME)
        Utils.setStr("Canvas", "view", self.view.get())
        Utils.setBool("Canvas", "axes", self.draw_axes.get())
        Utils.setBool("Canvas", "grid", self.draw_grid.get())
        Utils.setBool("Canvas", "margin", self.draw_margin.get())
        Utils.setBool("Canvas", "probe", self.draw_probe.get())
        Utils.setBool("Canvas", "paths", self.draw_paths.get())
        Utils.setBool("Canvas", "rapid", self.draw_rapid.get())
        Utils.setBool("Canvas", "workarea", self.draw_workarea.get())

    # ----------------------------------------------------------------------
    # Canvas toolbar FIXME XXX should be moved to CNCCanvas
    # ----------------------------------------------------------------------
    def createCanvasToolbar(self, toolbar):
        b = OptionMenu(toolbar, self.view, *VIEWS)
        b.config(padx=0, pady=1)
        b.unbind("F10")
        b.pack(side=LEFT)
        tkExtra.Balloon.set(b, _("Change viewing angle"))

        b = Button(
            toolbar, image=Utils.icons["zoom_in"],
            command=self.canvas.menuZoomIn
        )
        tkExtra.Balloon.set(b, _("Zoom In [Ctrl-=]"))
        b.pack(side=LEFT)

        b = Button(
            toolbar, image=Utils.icons["zoom_out"],
            command=self.canvas.menuZoomOut
        )
        tkExtra.Balloon.set(b, _("Zoom Out [Ctrl--]"))
        b.pack(side=LEFT)

        b = Button(
            toolbar, image=Utils.icons["zoom_on"],
            command=self.canvas.fit2Screen
        )
        tkExtra.Balloon.set(b, _("Fit to screen [F]"))
        b.pack(side=LEFT)

        Label(toolbar, text=_("Tool:"),
              image=Utils.icons["sep"], compound=LEFT).pack(
            side=LEFT, padx=2
        )
        # -----
        # Tools
        # -----
        b = Radiobutton(
            toolbar,
            image=Utils.icons["select"],
            indicatoron=FALSE,
            variable=self.canvas.actionVar,
            value=ACTION_SELECT,
            command=self.canvas.setActionSelect,
        )
        tkExtra.Balloon.set(b, _("Select tool [S]"))
        self.addWidget(b)
        b.pack(side=LEFT)

        b = Radiobutton(
            toolbar,
            image=Utils.icons["pan"],
            indicatoron=FALSE,
            variable=self.canvas.actionVar,
            value=ACTION_PAN,
            command=self.canvas.setActionPan,
        )
        tkExtra.Balloon.set(b, _("Pan viewport [X]"))
        b.pack(side=LEFT)

        b = Radiobutton(
            toolbar,
            image=Utils.icons["ruler"],
            indicatoron=FALSE,
            variable=self.canvas.actionVar,
            value=ACTION_RULER,
            command=self.canvas.setActionRuler,
        )
        tkExtra.Balloon.set(b, _("Ruler [R]"))
        b.pack(side=LEFT)

        # -----------
        # Draw flags
        # -----------
        Label(toolbar, text=_("Draw:"), image=Utils.icons["sep"],
              compound=LEFT).pack(
            side=LEFT, padx=2
        )

        b = Checkbutton(
            toolbar,
            image=Utils.icons["axes"],
            indicatoron=False,
            variable=self.draw_axes,
            command=self.drawAxes,
        )
        tkExtra.Balloon.set(b, _("Toggle display of axes"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["grid"],
            indicatoron=False,
            variable=self.draw_grid,
            command=self.drawGrid,
        )
        tkExtra.Balloon.set(b, _("Toggle display of grid lines"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["margins"],
            indicatoron=False,
            variable=self.draw_margin,
            command=self.drawMargin,
        )
        tkExtra.Balloon.set(b, _("Toggle display of margins"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            text="P",
            image=Utils.icons["measure"],
            indicatoron=False,
            variable=self.draw_probe,
            command=self.drawProbe,
        )
        tkExtra.Balloon.set(b, _("Toggle display of probe"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["endmill"],
            indicatoron=False,
            variable=self.draw_paths,
            command=self.toggleDrawFlag,
        )
        tkExtra.Balloon.set(b, _("Toggle display of paths (G1,G2,G3)"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["rapid"],
            indicatoron=False,
            variable=self.draw_rapid,
            command=self.toggleDrawFlag,
        )
        tkExtra.Balloon.set(b, _("Toggle display of rapid motion (G0)"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["workspace"],
            indicatoron=False,
            variable=self.draw_workarea,
            command=self.drawWorkarea,
        )
        tkExtra.Balloon.set(b, _("Toggle display of workarea"))
        b.pack(side=LEFT)

        b = Checkbutton(
            toolbar,
            image=Utils.icons["camera"],
            indicatoron=False,
            variable=self.draw_camera,
            command=self.drawCamera,
        )
        tkExtra.Balloon.set(b, _("Toggle display of camera"))
        b.pack(side=LEFT)
        if Camera.cv is None:
            b.config(state=DISABLED)

        b = Button(toolbar, image=Utils.icons["refresh"],
                   command=self.viewChange)
        tkExtra.Balloon.set(b, _("Redraw display [Ctrl-R]"))
        b.pack(side=LEFT)

        # -----------
        self.drawTime = tkExtra.Combobox(
            toolbar, width=3, background="White", command=self.drawTimeChange
        )
        tkExtra.Balloon.set(self.drawTime, _("Draw timeout in seconds"))
        self.drawTime.fill(
            ["inf", "1", "2", "3", "5", "10", "20", "30", "60", "120"])
        self.drawTime.set(DRAW_TIME)
        self.drawTime.pack(side=RIGHT)
        Label(toolbar, text=_("Timeout:")).pack(side=RIGHT)

    # ----------------------------------------------------------------------
    def redraw(self, event=None):
        self.canvas.reset()
        self.event_generate("<<ViewChange>>")

    # ----------------------------------------------------------------------
    def viewChange(self, a=None, b=None, c=None):
        self.event_generate("<<ViewChange>>")

    # ----------------------------------------------------------------------
    def viewPerspective(self, event=None):
        self.view.set(VIEWS[PROJECTION_PERSPECTIVE])

    # ----------------------------------------------------------------------
    def viewOrthographic(self, event=None):
        self.view.set(VIEWS[PROJECTION_ORTHOGRAPHIC])

    # ----------------------------------------------------------------------
    def toggleDrawFlag(self):
        self.canvas.draw_axes = self.draw_axes.get()
        self.canvas.draw_grid = self.draw_grid.get()
        self.canvas.draw_margin = self.draw_margin.get()
        self.canvas.draw_probe = self.draw_probe.get()
        self.canvas.draw_paths = self.draw_paths.get()
        self.canvas.draw_rapid = self.draw_rapid.get()
        self.canvas.draw_workarea = self.draw_workarea.get()
        self.event_generate("<<ViewChange>>")

    # ----------------------------------------------------------------------
    def drawAxes(self, value=None):
        if value is not None:
            self.draw_axes.set(value)
        self.canvas.draw_axes = self.draw_axes.get()
        self.canvas.drawAxes()

    # ----------------------------------------------------------------------
    def drawGrid(self, value=None):
        if value is not None:
            self.draw_grid.set(value)
        self.canvas.draw_grid = self.draw_grid.get()
        self.canvas.drawGrid()

    # ----------------------------------------------------------------------
    def drawMargin(self, value=None):
        if value is not None:
            self.draw_margin.set(value)
        self.canvas.draw_margin = self.draw_margin.get()
        self.canvas.drawMargin()

    # ----------------------------------------------------------------------
    def drawProbe(self, value=None):
        if value is not None:
            self.draw_probe.set(value)
        self.canvas.draw_probe = self.draw_probe.get()
        self.canvas.drawProbe()

    # ----------------------------------------------------------------------
    def drawWorkarea(self, value=None):
        if value is not None:
            self.draw_workarea.set(value)
        self.canvas.draw_workarea = self.draw_workarea.get()
        self.canvas.drawWorkarea()

    # ----------------------------------------------------------------------
    def drawCamera(self, value=None):
        if value is not None:
            self.draw_camera.set(value)
        if self.draw_camera.get():
            self.canvas.cameraOn()
        else:
            self.canvas.cameraOff()

    # ----------------------------------------------------------------------
    def drawTimeChange(self):
        global DRAW_TIME
        try:
            DRAW_TIME = int(self.drawTime.get())
        except ValueError:
            DRAW_TIME = 5 * 60
        self.viewChange()
