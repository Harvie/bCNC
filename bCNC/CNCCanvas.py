# $Id: CNCCanvas.py,v 1.7 2014/10/15 15:04:06 bnv Exp $
#
# Author:       vvlachoudis@gmail.com
# Date: 24-Aug-2014

import math
import time
import sys
import hashlib
from collections import Counter

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
        self._last = (0.0, 0.0, 0.0)
        self.selected_items = []
        self.fbo = None
        self.texture = None
        self.picking_buffer = None
        self._picking_mode = False

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
        self._info_items = []
        self._probe_texture = None
        self._probe_hash = None
        self._path_coords = {}
        self._full_path_cache = {}
        self._camera_on = False
        self._camera_texture = None
        self._active_item = None

        self.reset()
        self.initPosition()

    def to_id_color(self, bid, lid):
        """Convert block and line id to a unique color."""
        # Combine bid and lid into a single 24-bit ID.
        # This assumes lid < 1024 and bid < 16384.
        path_id = ((bid & 0x3FFF) << 10) | (lid & 0x3FF)
        path_id += 1  # a path_id of 0 is reserved for the background
        r = (path_id >> 16) & 0xFF
        g = (path_id >> 8) & 0xFF
        b = path_id & 0xFF
        return (r / 255.0, g / 255.0, b / 255.0)

    def from_id_color(self, color):
        """Convert a color back to a block and line id."""
        r, g, b = color  # color is a tuple of integers (0-255)
        path_id = (r << 16) | (g << 8) | b
        if path_id == 0:
            return None, None
        path_id -= 1
        bid = path_id >> 10
        lid = path_id & 0x3FF
        return bid, lid

    def init_fbo(self):
        """Initialize the framebuffer object"""
        self.fbo = glGenFramebuffers(1)
        self.texture = glGenTextures(1)
        glBindTexture(GL_TEXTURE_2D, self.texture)
        glTexImage2D(GL_TEXTURE_2D, 0, GL_RGB, self.winfo_width(), self.winfo_height(), 0, GL_RGB, GL_UNSIGNED_BYTE, None)
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR)
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR)
        glBindFramebuffer(GL_FRAMEBUFFER, self.fbo)
        glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, self.texture, 0)
        self.picking_buffer = glGenRenderbuffers(1)
        glBindRenderbuffer(GL_RENDERBUFFER, self.picking_buffer)
        glRenderbufferStorage(GL_RENDERBUFFER, GL_DEPTH_COMPONENT, self.winfo_width(), self.winfo_height())
        glFramebufferRenderbuffer(GL_FRAMEBUFFER, GL_DEPTH_ATTACHMENT, GL_RENDERBUFFER, self.picking_buffer)
        glBindFramebuffer(GL_FRAMEBUFFER, 0)


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

        if self.action == ACTION_RULER:
            self._vx0, self._vy0, self._vz0 = self.canvas2xyz(event.x, event.y)
            self._vector = [self._vx0, self._vy0, self._vz0, self._vx0, self._vy0, self._vz0]
            self._mouseAction = ACTION_RULER
            return

        if event.state & CONTROLSHIFT_MASK == CONTROLSHIFT_MASK:
            self.actionGantry(event.x, event.y)
            return

        elif self.action == ACTION_SELECT:
            self._mouseAction = ACTION_SELECT_SINGLE

        elif self.action == ACTION_MOVE:
            self._mouseAction = ACTION_MOVE
            self._vx0, self._vy0, self._vz0 = self.canvas2xyz(event.x, event.y)
            #self.app.select_all()

        elif self.action == ACTION_RULER:
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
            self._mouseAction = ACTION_PAN

    # ----------------------------------------------------------------------
    # Canvas motion button 1
    # ----------------------------------------------------------------------
    def buttonMotion(self, event):
        # If we started a selection, check if we've dragged far enough to be a rotation
        if self._mouseAction == ACTION_SELECT_SINGLE:
            dist_sq = (event.x - self._xp)**2 + (event.y - self._yp)**2
            if dist_sq > (CLOSE_DISTANCE**2):
                self._mouseAction = ACTION_ROTATE

        dx = event.x - self._x
        dy = event.y - self._y

        # Perform action based on the current mouse action
        if self._mouseAction == ACTION_ROTATE:
            self.r[0] += dy
            self.r[1] += dx
        elif self._mouseAction == ACTION_PAN:
            self.t[0] += dx * 0.1
            self.t[1] -= dy * 0.1
        elif self._mouseAction == ACTION_RULER:
            self._vx1, self._vy1, self._vz1 = self.canvas2xyz(event.x, event.y)
            self._vector[3:] = [self._vx1, self._vy1, self._vz1]
            dx_ruler = self._vx1 - self._vx0
            dy_ruler = self._vy1 - self._vy0
            dz_ruler = self._vz1 - self._vz0
            self.status(
                _("dx={:g}  dy={:g}  dz={:g}  length={:g}  angle={:g}").format(
                    dx_ruler,
                    dy_ruler,
                    dz_ruler,
                    math.sqrt(dx_ruler**2 + dy_ruler**2 + dz_ruler**2),
                    math.degrees(math.atan2(dy_ruler, dx_ruler)),
                )
            )
        elif self._mouseAction == ACTION_MOVE:
            self._vx1, self._vy1, self._vz1 = self.canvas2xyz(event.x, event.y)
            dx_move = self._vx1 - self._vx0
            dy_move = self._vy1 - self._vy0
            dz_move = self._vz1 - self._vz0
            self.gcode.moveLines(self.selected_items, dx_move, dy_move, dz_move)
            self._vx0, self._vy0, self._vz0 = self._vx1, self._vy1, self._vz1

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
            # --- Picking Logic ---
            self.drawForPicking()

            # This should be called only if the FBO exists
            if not self.fbo:
                self._mouseAction = None
                return

            glBindFramebuffer(GL_FRAMEBUFFER, self.fbo)
            x = event.x
            y = self.winfo_height() - event.y  # Y is inverted in OpenGL

            # Read a small area around the cursor to give a selection margin
            margin = 2  # Results in a 5x5 pixel area
            x_start = x - margin
            y_start = y - margin
            width = height = margin * 2 + 1

            # Clamp the read area to be within the framebuffer dimensions
            x_start = max(0, min(x_start, self.winfo_width() - width))
            y_start = max(0, min(y_start, self.winfo_height() - height))

            pixels = glReadPixels(x_start, y_start, width, height, GL_RGB, GL_UNSIGNED_BYTE)
            glBindFramebuffer(GL_FRAMEBUFFER, 0)

            # Find the most common non-background ID in the area
            ids = []
            if len(pixels) > 0:
                for i in range(0, len(pixels), 3):
                    color = (pixels[i], pixels[i+1], pixels[i+2])
                    bid_cand, lid_cand = self.from_id_color(color)
                    if bid_cand is not None:
                        ids.append((bid_cand, lid_cand))

            if ids:
                # Use Counter to find the most frequent ID
                bid, lid = Counter(ids).most_common(1)[0][0]
            else:
                bid, lid = None, None

            new_selection = []
            if bid is not None and lid is not None:
                block = self.gcode.blocks[bid]
                if block.expand:
                    # Select single line
                    new_selection.append((bid, lid))
                else:
                    # Select whole block
                    new_selection.extend([(bid, i) for i in range(len(block))])

            # Handle selection logic
            is_replace = event.state & CONTROL_MASK == 0
            if is_replace:
                self.selected_items = new_selection
            else:  # Control is pressed, toggle selection
                for item in new_selection:
                    if item in self.selected_items:
                        self.selected_items.remove(item)
                    else:
                        self.selected_items.append(item)

            self.app.select(
                self.selected_items,
                self._mouseAction == ACTION_SELECT_DOUBLE,
                is_replace,
            )
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
            self._mouseAction = None

        elif self._mouseAction == ACTION_PAN:
            self.setAction(ACTION_SELECT)

        elif self._mouseAction == ACTION_ROTATE:
            self._mouseAction = None

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
        if not self.selected_items:
            return 0.0, 0.0

        min_x, max_x = float('inf'), float('-inf')
        min_y, max_y = float('inf'), float('-inf')

        for bid, lid in self.selected_items:
            path = self._full_path_cache.get((bid, lid))
            if not path:
                continue

            for x, y, z in path:
                if x < min_x: min_x = x
                if x > max_x: max_x = x
                if y < min_y: min_y = y
                if y > max_y: max_y = y

        if min_x == float('inf'): # Nothing was found
            return 0.0, 0.0

        return max_x - min_x, max_y - min_y

    def resize_fbo(self):
        """Resize framebuffer object attachments"""
        width = self.winfo_width()
        height = self.winfo_height()
        if width <= 0 or height <= 0:
            return

        # Ensure we are on the right context
        self.make_current()

        glBindTexture(GL_TEXTURE_2D, self.texture)
        glTexImage2D(GL_TEXTURE_2D, 0, GL_RGB, width, height, 0, GL_RGB, GL_UNSIGNED_BYTE, None)

        glBindRenderbuffer(GL_RENDERBUFFER, self.picking_buffer)
        glRenderbufferStorage(GL_RENDERBUFFER, GL_DEPTH_COMPONENT, width, height)

        # Unbind
        glBindTexture(GL_TEXTURE_2D, 0)
        glBindRenderbuffer(GL_RENDERBUFFER, 0)

    # ----------------------------------------------------------------------
    def configureEvent(self, event):
        if self.fbo is None:
            self.init_fbo()
        else:
            self.resize_fbo()
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

        if w == 0 or h == 0:
            return

        self.scale = 0.8 * min(self.winfo_width() / w, self.winfo_height() / h)
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
        self.selected_items = []
        self.draw()

    def activeMarker(self, item=None):
        """Highlight the active gcode line"""
        if self._active_item != item:
            self._active_item = item
            self.draw()

    # ----------------------------------------------------------------------
    # Highlight selected items
    # ----------------------------------------------------------------------
    def select(self, items):
        self.selected_items = items
        self.draw()

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
        self._info_items = []
        if not blocks:
            self.draw()
            return

        for block in blocks:
            # Bounding box
            bbox = (
                block.xmin,
                block.ymin,
                block.zmin,
                block.xmax,
                block.ymax,
                block.zmax,
            )
            self._info_items.append(("box", bbox))

            # Direction arrow
            if block.start and block.end and block.start != block.end:
                self._info_items.append(("arrow", (block.start, block.end)))
        self.draw()

    # -----------------------------------------------------------------------
    def cameraOn(self, event=None):
        if not self.camera.start():
            return
        self._camera_on = True
        self.cameraRefresh()

    # -----------------------------------------------------------------------
    def cameraOff(self, event=None):
        self._camera_on = False
        if self._camera_texture is not None:
            self.make_current()
            glDeleteTextures([self._camera_texture])
            self._camera_texture = None

        if self._cameraAfter:
            self.after_cancel(self._cameraAfter)
            self._cameraAfter = None

        if self.camera.isOn():
            self.camera.stop()
        self.draw()

    # -----------------------------------------------------------------------
    def cameraUpdate(self):
        if not self.camera.isOn():
            return
        if self._cameraAfter:
            self.after_cancel(self._cameraAfter)
            self._cameraAfter = None
        self.cameraRefresh()

    # -----------------------------------------------------------------------
    def cameraRefresh(self):
        if not self._camera_on:
            return

        if not self.camera.read():
            self.cameraOff()
            return

        # I am not sure what all this processing does, but I will keep it
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

        # Get image data and update texture
        image_data = self.camera.image
        if image_data is not None:
            self.make_current()
            if self._camera_texture is None:
                self._camera_texture = glGenTextures(1)
                glBindTexture(GL_TEXTURE_2D, self._camera_texture)
                glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR)
                glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR)

            glBindTexture(GL_TEXTURE_2D, self._camera_texture)
            h, w = image_data.shape[:2]

            # Convert BGR to RGB for OpenGL
            if len(image_data.shape) == 3 and image_data.shape[2] == 3:
                image_data = image_data[:, :, ::-1]

            glTexImage2D(GL_TEXTURE_2D, 0, GL_RGB, w, h, 0, GL_RGB, GL_UNSIGNED_BYTE, image_data)
            glBindTexture(GL_TEXTURE_2D, 0)

        self.draw()
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
        # This method is now obsolete. The positioning is handled
        # by the new drawCameraOverlay() method's transformation matrix.
        # I will leave it here as a stub for now.
        pass

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
        glClearColor(1.0, 1.0, 1.0, 1.0)
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
            w = self.winfo_width() / self.scale / 2
            h = self.winfo_height() / self.scale / 2
            glOrtho(-w, w, -h, h, -1000, 1000)

    def set_modelview(self,):
        """Setup the modelview matrix"""
        glMatrixMode(GL_MODELVIEW)
        glLoadIdentity()
        glTranslatef(self.t[0], self.t[1], self.t[2]-400)
        glRotatef(self.r[0], 1, 0, 0)
        glRotatef(self.r[1], 0, 1, 0)
        glRotatef(self.r[2], 0, 0, 1)
        glScalef(self.scale, self.scale, self.scale)

    def drawForPicking(self):
        if self._inDraw:
            return
        self._inDraw = True
        self._picking_mode = True

        try:
            # This should be called only if the FBO exists
            if not self.fbo: return

            glBindFramebuffer(GL_FRAMEBUFFER, self.fbo)
            self.make_current()
            self.init_opengl() # This sets projection and modelview
            # Clear to a color that means "nothing" (ID 0)
            glClearColor(0.0, 0.0, 0.0, 0.0)
            glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT)

            # Only draw paths for picking
            self.drawPaths()

            glFlush() # Ensure all drawing commands are executed
        finally:
            glBindFramebuffer(GL_FRAMEBUFFER, 0)
            self._inDraw = False
            self._picking_mode = False
            # Restore clear color for normal drawing
            glClearColor(1.0, 1.0, 1.0, 1.0)

    def drawInfo(self):
        if not self._info_items:
            return

        glLineWidth(2.0)
        # Gold color for info items
        glColor3f(1.0, 0.84, 0.0)
        glLineStipple(1, 0xAAAA)
        glEnable(GL_LINE_STIPPLE)

        for type, data in self._info_items:
            if type == 'box':
                xmin, ymin, zmin, xmax, ymax, zmax = data
                # Draw a 3D bounding box
                glBegin(GL_LINE_LOOP)
                glVertex3f(xmin, ymin, zmin)
                glVertex3f(xmax, ymin, zmin)
                glVertex3f(xmax, ymax, zmin)
                glVertex3f(xmin, ymax, zmin)
                glEnd()
                glBegin(GL_LINE_LOOP)
                glVertex3f(xmin, ymin, zmax)
                glVertex3f(xmax, ymin, zmax)
                glVertex3f(xmax, ymax, zmax)
                glVertex3f(xmin, ymax, zmax)
                glEnd()
                glBegin(GL_LINES)
                glVertex3f(xmin, ymin, zmin)
                glVertex3f(xmin, ymin, zmax)
                glVertex3f(xmax, ymin, zmin)
                glVertex3f(xmax, ymin, zmax)
                glVertex3f(xmax, ymax, zmin)
                glVertex3f(xmax, ymax, zmax)
                glVertex3f(xmin, ymax, zmin)
                glVertex3f(xmin, ymax, zmax)
                glEnd()
            elif type == 'arrow':
                start, end = data
                glBegin(GL_LINES)
                glVertex3f(*start)
                glVertex3f(*end)
                glEnd()
        glDisable(GL_LINE_STIPPLE)

    def drawSelectionHighlights(self):
        if not self.selected_items:
            return

        glLineWidth(2.0)
        glColor3f(0.0, 0.0, 1.0)  # Blue, to match selection color

        for bid, lid in self.selected_items:
            coords = self._path_coords.get((bid, lid))
            if not coords:
                continue

            start_point, end_point = coords
            if start_point == end_point:
                continue

            # Vector from start to end
            dx = end_point[0] - start_point[0]
            dy = end_point[1] - start_point[1]
            dz = end_point[2] - start_point[2]

            # Normalize the vector
            length = math.sqrt(dx * dx + dy * dy + dz * dz)
            if length == 0:
                continue
            dx /= length
            dy /= length
            dz /= length

            # Arrowhead size
            arrow_size = self.scale * 0.2
            if arrow_size < 0.5: arrow_size = 0.5
            if arrow_size > 2.0: arrow_size = 2.0

            # Arrow base point
            base_point = (
                end_point[0] - dx * arrow_size,
                end_point[1] - dy * arrow_size,
                end_point[2] - dz * arrow_size,
            )

            # Perpendicular vector for arrowhead base using cross product
            # Find a vector that is not parallel to the direction vector
            if abs(dx) > 0.1 or abs(dy) > 0.1:
                up_vec = (0.0, 0.0, 1.0) # World up
            else:
                up_vec = (1.0, 0.0, 0.0) # World right

            p_dx = dy * up_vec[2] - dz * up_vec[1]
            p_dy = dz * up_vec[0] - dx * up_vec[2]
            p_dz = dx * up_vec[1] - dy * up_vec[0]
            p_len = math.sqrt(p_dx**2 + p_dy**2 + p_dz**2)
            p_dx /= p_len
            p_dy /= p_len
            p_dz /= p_len

            # Arrowhead base vertices
            v1 = (
                base_point[0] + p_dx * arrow_size * 0.4,
                base_point[1] + p_dy * arrow_size * 0.4,
                base_point[2] + p_dz * arrow_size * 0.4,
            )
            v2 = (
                base_point[0] - p_dx * arrow_size * 0.4,
                base_point[1] - p_dy * arrow_size * 0.4,
                base_point[2] - p_dz * arrow_size * 0.4,
            )

            # Draw a simple triangle arrowhead
            glBegin(GL_TRIANGLES)
            glVertex3f(*end_point)
            glVertex3f(*v1)
            glVertex3f(*v2)
            glEnd()

    def getCameraPosition(self, w, h):
        canvas_w = self.winfo_width()
        canvas_h = self.winfo_height()

        if self.cameraAnchor == NONE:
            if self._lastGantry is not None:
                # Project 3D gantry position to 2D screen coordinates
                try:
                    modelview = glGetDoublev(GL_MODELVIEW_MATRIX)
                    projection = glGetDoublev(GL_PROJECTION_MATRIX)
                    viewport = glGetIntegerv(GL_VIEWPORT)
                    x, y, z = gluProject(self._lastGantry[0], self._lastGantry[1], self._lastGantry[2], modelview, projection, viewport)
                    return x - w/2, y - h/2
                except GLError:
                    return (canvas_w - w) / 2, (canvas_h - h) / 2 # Default to center
            else:
                return (canvas_w - w) / 2, (canvas_h - h) / 2 # Default to center
        else:
            # Logic for anchors like NW, S, E, etc.
            x = (canvas_w - w) / 2
            y = (canvas_h - h) / 2
            if N in self.cameraAnchor: y = canvas_h - h
            elif S in self.cameraAnchor: y = 0
            if W in self.cameraAnchor: x = 0
            elif E in self.cameraAnchor: x = canvas_w - w
            return x, y

    def drawCameraOverlay(self):
        if not self._camera_on or self._camera_texture is None or self.camera.image is None:
            return

        width = self.winfo_width()
        height = self.winfo_height()

        # --- Switch to 2D orthographic projection ---
        glMatrixMode(GL_PROJECTION)
        glPushMatrix()
        glLoadIdentity()
        glOrtho(0, width, 0, height, -1, 1)

        glMatrixMode(GL_MODELVIEW)
        glPushMatrix()
        glLoadIdentity()

        glDisable(GL_DEPTH_TEST)
        glEnable(GL_BLEND)
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)

        # --- Draw Camera Texture ---
        h, w = self.camera.image.shape[:2]
        x, y = self.getCameraPosition(w, h)

        glColor4f(1.0, 1.0, 1.0, 0.8)
        glEnable(GL_TEXTURE_2D)
        glBindTexture(GL_TEXTURE_2D, self._camera_texture)
        glBegin(GL_QUADS)
        glTexCoord2f(0.0, 0.0); glVertex2f(x, y)
        glTexCoord2f(1.0, 0.0); glVertex2f(x + w, y)
        glTexCoord2f(1.0, 1.0); glVertex2f(x + w, y + h)
        glTexCoord2f(0.0, 1.0); glVertex2f(x, y + h)
        glEnd()
        glDisable(GL_TEXTURE_2D)

        # --- Draw Crosshairs and Circles ---
        glColor4f(0.0, 1.0, 1.0, 1.0) # Cyan
        glLineWidth(1.0)

        glBegin(GL_LINES)
        glVertex2f(x, y + h/2)
        glVertex2f(x + w, y + h/2)
        glVertex2f(x + w/2, y)
        glVertex2f(x + w/2, y + h)
        glEnd()

        r = self.cameraR * self.cameraScale
        center_x = x + w/2
        center_y = y + h/2

        glBegin(GL_LINE_LOOP)
        for i in range(360):
            rad = math.radians(i)
            glVertex2f(center_x + math.cos(rad) * r, center_y + math.sin(rad) * r)
        glEnd()

        glLineStipple(1, 0x3333)
        glEnable(GL_LINE_STIPPLE)
        glBegin(GL_LINE_LOOP)
        for i in range(360):
            rad = math.radians(i)
            glVertex2f(center_x + math.cos(rad) * r * 2, center_y + math.sin(rad) * r * 2)
        glEnd()
        glDisable(GL_LINE_STIPPLE)

        # --- Restore 3D projection and state ---
        glEnable(GL_DEPTH_TEST)
        glDisable(GL_BLEND)
        glMatrixMode(GL_PROJECTION)
        glPopMatrix()
        glMatrixMode(GL_MODELVIEW)
        glPopMatrix()

    # ----------------------------------------------------------------------
    # Parse and draw the file from the editor to g-code commands
    # ----------------------------------------------------------------------
    def draw(self, view=None):
        if self._inDraw:
            return
        self._inDraw = True

        if view is not None:
            if view == "Perspective":
                self.projection = PROJECTION_PERSPECTIVE
            elif view == "Orthographic":
                self.projection = PROJECTION_ORTHOGRAPHIC

        self.make_current()
        self.init_opengl()
        glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT)

        self.drawPaths()
        self.drawGrid()
        self.drawMargin()
        self.drawWorkarea()
        self.drawProbe()
        self.drawOrient()
        self.drawAxes()
        self._drawVector()
        self.drawInfo()
        self.drawSelectionHighlights()
        self.drawCameraOverlay()
        self.swap_buffers()

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

    def _drawVector(self):
        if self._vector is None:
            return
        glColor3f(0.0, 1.0, 0.0)
        glLineWidth(1.0)
        glBegin(GL_LINES)
        glVertex3f(*self._vector[:3])
        glVertex3f(*self._vector[3:])
        glEnd()

    def _drawCone(self, base_center, tip, radius, num_segments=12):
        # Vector from base to tip (cone's axis)
        axis_x = tip[0] - base_center[0]
        axis_y = tip[1] - base_center[1]
        axis_z = tip[2] - base_center[2]
        axis_len = math.sqrt(axis_x**2 + axis_y**2 + axis_z**2)
        if axis_len == 0: return
        axis_x /= axis_len
        axis_y /= axis_len
        axis_z /= axis_len

        # Find a perpendicular vector to define the plane of the cone's base
        if abs(axis_x) > 0.1 or abs(axis_y) > 0.1:
            up_vec = (0.0, 0.0, 1.0) # World up
        else:
            up_vec = (1.0, 0.0, 0.0) # World right

        # First basis vector for the circle (u) via cross product
        u_x = axis_y * up_vec[2] - axis_z * up_vec[1]
        u_y = axis_z * up_vec[0] - axis_x * up_vec[2]
        u_z = axis_x * up_vec[1] - axis_y * up_vec[0]
        u_len = math.sqrt(u_x**2 + u_y**2 + u_z**2)
        u_x /= u_len
        u_y /= u_len
        u_z /= u_len

        # Second basis vector for the circle (v) via cross product
        v_x = u_y * axis_z - u_z * axis_y
        v_y = u_z * axis_x - u_x * axis_z
        v_z = u_x * axis_y - u_y * axis_x

        # Draw the cone surface
        glBegin(GL_TRIANGLE_FAN)
        glVertex3f(*tip)
        for i in range(num_segments + 1):
            angle = i * (2 * math.pi / num_segments)
            # Position on the circle
            px = base_center[0] + radius * (math.cos(angle) * u_x + math.sin(angle) * v_x)
            py = base_center[1] + radius * (math.cos(angle) * u_y + math.sin(angle) * v_y)
            pz = base_center[2] + radius * (math.cos(angle) * u_z + math.sin(angle) * v_z)
            glVertex3f(px, py, pz)
        glEnd()

        # Draw the base circle
        glBegin(GL_TRIANGLE_FAN)
        for i in range(num_segments + 1):
            angle = i * (2 * math.pi / num_segments)
            # Position on the circle
            px = base_center[0] + radius * (math.cos(angle) * u_x + math.sin(angle) * v_x)
            py = base_center[1] + radius * (math.cos(angle) * u_y + math.sin(angle) * v_y)
            pz = base_center[2] + radius * (math.cos(angle) * u_z + math.sin(angle) * v_z)
            glVertex3f(px, py, pz)
        glEnd()

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

        # Draw toolbit cone
        glColor3f(1.0, 0.0, 0.0) # Red
        tool_length = 20.0
        tool_radius = 4.0
        base = (x, y, z)
        tip = (x, y, z - tool_length)
        self._drawCone(base, tip, tool_radius)

    # ----------------------------------------------------------------------
    # Draw system axes
    # ----------------------------------------------------------------------
    def drawAxes(self):
        if not self.draw_axes:
            return
        glLineWidth(1.0)

        # Draw axis lines
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

        # Draw arrowheads
        arrow_length = 2.0
        arrow_radius = 0.5

        # X-axis arrowhead
        glColor3f(1.0, 0.0, 0.0)
        base = (10.0, 0.0, 0.0)
        tip = (10.0 + arrow_length, 0.0, 0.0)
        self._drawCone(base, tip, arrow_radius)

        # Y-axis arrowhead
        glColor3f(0.0, 1.0, 0.0)
        base = (0.0, 10.0, 0.0)
        tip = (0.0, 10.0 + arrow_length, 0.0)
        self._drawCone(base, tip, arrow_radius)

        # Z-axis arrowhead
        glColor3f(0.0, 0.0, 1.0)
        base = (0.0, 0.0, 10.0)
        tip = (0.0, 0.0, 10.0 + arrow_length)
        self._drawCone(base, tip, arrow_radius)


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
        glColor3f(0.8, 0.8, 0.8)
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


    def updateProbeTexture(self):
        if self._probe_texture:
            glDeleteTextures([self._probe_texture])
            self._probe_texture = None
            self._probe_hash = None

        probe = self.gcode.probe
        if probe.isEmpty() or not probe.cols or not probe.rows or not probe.points:
            return

        z_values = numpy.array([p[2] for p in probe.points])
        z_min, z_max = z_values.min(), z_values.max()

        if z_max == z_min:
            normalized = numpy.zeros(z_values.shape)
        else:
            normalized = (z_values - z_min) / (z_max - z_min)

        try:
            normalized = normalized.reshape((probe.rows, probe.cols))
        except ValueError:
            # Data doesn't fit grid, can't create image
            return

        # Simple colormap: blue (low) -> green -> red (high)
        # Create an (rows, cols, 3) RGB image array
        image_data = numpy.zeros((probe.rows, probe.cols, 3), dtype=numpy.uint8)
        # Blue to Cyan to Green to Yellow to Red
        r = (255 * numpy.clip(2 * normalized - 1, 0, 1)).astype(numpy.uint8)
        g = (255 * (1 - 2 * numpy.abs(normalized - 0.5))).astype(numpy.uint8)
        b = (255 * numpy.clip(1 - 2 * normalized, 0, 1)).astype(numpy.uint8)

        image_data[..., 0] = r
        image_data[..., 1] = g
        image_data[..., 2] = b

        self._probe_texture = glGenTextures(1)
        glBindTexture(GL_TEXTURE_2D, self._probe_texture)
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR)
        glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR)
        glTexImage2D(GL_TEXTURE_2D, 0, GL_RGB, probe.cols, probe.rows, 0, GL_RGB, GL_UNSIGNED_BYTE, numpy.flipud(image_data))
        glBindTexture(GL_TEXTURE_2D, 0)
        self._probe_hash = hashlib.sha1(z_values.tobytes()).hexdigest()

    def drawProbeImage(self):
        if self._probe_texture is None: return
        probe = self.gcode.probe
        if probe.isEmpty(): return

        # Blend texture with background
        glEnable(GL_BLEND)
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
        glColor4f(1.0, 1.0, 1.0, 0.7) # Set color to white to not tint the texture
        glEnable(GL_TEXTURE_2D)
        glBindTexture(GL_TEXTURE_2D, self._probe_texture)

        z = probe.zmin if self.app.probe.get("probe_surface_z") == "min" else probe.zmax

        glBegin(GL_QUADS)
        glTexCoord2f(0.0, 0.0); glVertex3f(probe.xmin, probe.ymin, z)
        glTexCoord2f(1.0, 0.0); glVertex3f(probe.xmax, probe.ymin, z)
        glTexCoord2f(1.0, 1.0); glVertex3f(probe.xmax, probe.ymax, z)
        glTexCoord2f(0.0, 1.0); glVertex3f(probe.xmin, probe.ymax, z)
        glEnd()

        glDisable(GL_TEXTURE_2D)
        glDisable(GL_BLEND)

    # ----------------------------------------------------------------------
    # Display probe
    # ----------------------------------------------------------------------
    def drawProbe(self):
        if not self.draw_probe or self.gcode.probe.isEmpty():
            if self._probe_texture:
                glDeleteTextures([self._probe_texture])
                self._probe_texture = None
                self._probe_hash = None
            return

        # Check if probe data changed
        new_hash = hashlib.sha1(numpy.array(self.gcode.probe.points).tobytes()).hexdigest()
        if new_hash != self._probe_hash:
            self.updateProbeTexture()

        # Draw the image surface
        self.drawProbeImage()

        probe = self.gcode.probe

        # Draw probe grid
        glColor3f(1.0, 1.0, 0.0)
        glBegin(GL_LINES)
        if probe.xstep() > 0:
            for x in bmath.frange(probe.xmin, probe.xmax + 0.00001, probe.xstep()):
                glVertex3f(x, probe.ymin, 0.0)
                glVertex3f(x, probe.ymax, 0.0)
        if probe.ystep() > 0:
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
            self._path_coords.clear()
            self._full_path_cache.clear()
            drawG = self.draw_rapid or self.draw_paths or self.draw_margin
            for i, block in enumerate(self.gcode.blocks):
                start = True  # start location found
                block.resetPath()
                block.bid = i

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
                        path = self.drawPath(block, j, cmd)
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
    def drawPath(self, block, j, cmds):
        self.cnc.motionStart(cmds)
        xyz = self.cnc.motionPath()
        self.cnc.motionEnd()
        if xyz:
            self._path_coords[(block.bid, j)] = (xyz[0], xyz[-1])
            self._full_path_cache[(block.bid, j)] = xyz
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

            # set color and line width
            is_active = (block.bid, j) == self._active_item
            is_selected = (block.bid, j) in self.selected_items
            is_enabled = block.enable

            if self._picking_mode:
                r, g, b = self.to_id_color(block.bid, j)
                glColor3f(r, g, b)
                glDisable(GL_LINE_STIPPLE)
            elif is_active:
                glColor3f(1.0, 0.65, 0.0)  # Orange for active
                glLineWidth(2.0)
                glDisable(GL_LINE_STIPPLE)
            elif not is_enabled:
                glLineWidth(1.0)
                glDisable(GL_LINE_STIPPLE)
                if is_selected:
                    glColor3f(0.25, 0.88, 0.82)  # Turquoise for disabled+selected
                else:
                    glColor3f(0.75, 0.75, 0.75)  # Light Gray for disabled
            elif is_selected:
                glColor3f(0.0, 0.0, 1.0)  # Blue for selected
                glLineWidth(1.0) # Ensure it's normal width
                glDisable(GL_LINE_STIPPLE)
            elif self.cnc.gcode == 0:
                if self.draw_rapid:
                    glColor3f(0.5, 0.5, 0.5)
                    glLineStipple(1, 0x3333)
                    glEnable(GL_LINE_STIPPLE)
            elif self.draw_paths:
                glColor3f(0.0, 0.0, 0.0)
                glDisable(GL_LINE_STIPPLE)

            glBegin(GL_LINE_STRIP)
            for x, y, z in xyz:
                glVertex3f(x, y, z)
            glEnd()

            # Reset line width if it was changed
            if is_active:
                glLineWidth(1.0)

            glDisable(GL_LINE_STIPPLE)

        return (block.bid, j)


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

        self.canvas = CNCCanvas(self, app)
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
        self.canvas.draw()

    # ----------------------------------------------------------------------
    def drawGrid(self, value=None):
        if value is not None:
            self.draw_grid.set(value)
        self.canvas.draw_grid = self.draw_grid.get()
        self.canvas.draw()

    # ----------------------------------------------------------------------
    def drawMargin(self, value=None):
        if value is not None:
            self.draw_margin.set(value)
        self.canvas.draw_margin = self.draw_margin.get()
        self.canvas.draw()

    # ----------------------------------------------------------------------
    def drawProbe(self, value=None):
        if value is not None:
            self.draw_probe.set(value)
        self.canvas.draw_probe = self.draw_probe.get()
        self.canvas.draw()

    # ----------------------------------------------------------------------
    def drawWorkarea(self, value=None):
        if value is not None:
            self.draw_workarea.set(value)
        self.canvas.draw_workarea = self.draw_workarea.get()
        self.canvas.draw()

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
