from picoware.system.vector import Vector # Import Vector class for 2D screen coordinates
from picoware.system.colors import TFT_WHITE, TFT_BLACK, TFT_BLUE, TFT_CYAN, TFT_YELLOW # Import required display hex colors
from picoware.system.buttons import BUTTON_BACK, BUTTON_ESCAPE # Import hardware back AND escape button mapping
import math # Import math library strictly for initial lookup table generation
import random # Import random library to scatter snowflakes naturally
import time # Import time library to handle the 5-second initial delay
BUTTON_G = 13 # Map the 'g' key manually to integer 13 to avoid framework import issues
BUTTON_R = 24 # Map the 'r' key manually to integer 24 to avoid framework import issues

# --- DYNAMIC RESOLUTION VARIABLES ---
SCREEN_W = 320 # Fallback width, will be dynamically overwritten by actual hardware size
SCREEN_H = 240 # Fallback height, will be dynamically overwritten by actual hardware size
CX = 160 # Fallback horizontal center, will be dynamically overwritten
CY = 120 # Fallback vertical center, will be dynamically overwritten
GROUND_CHUNKS = 80 # Fallback chunk count, will be dynamically overwritten

# --- LOGO & PHYSICS SETTINGS ---
LOGO_W = 90 # Define the total width of the rotating logo bounding box
LOGO_H = 24 # Define the total height of the rotating logo bounding box
L_LEFT = -45 # Hardcode local left edge of the logo for maximum speed
L_RIGHT = 45 # Hardcode local right edge of the logo for maximum speed
L_TOP = -12 # Hardcode local top edge of the logo for maximum speed
L_BOT = 12 # Hardcode local bottom edge of the logo for maximum speed

# Custom Vectorized Text: "SLASHER006"
LOGO_LINES = [ # Define the start and end points for the custom vectorized letters
    (-39, -6, -34, -6), (-39, -6, -39, 0), (-39, 0, -34, 0), (-34, 0, -34, 6), (-34, 6, -39, 6), # Letter S
    (-31, -6, -31, 6), (-31, 6, -26, 6), # Letter L
    (-23, 6, -23, -6), (-23, -6, -18, -6), (-18, -6, -18, 6), (-23, 0, -18, 0), # Letter A
    (-15, -6, -10, -6), (-15, -6, -15, 0), (-15, 0, -10, 0), (-10, 0, -10, 6), (-10, 6, -15, 6), # Letter S
    (-7, -6, -7, 6), (-2, -6, -2, 6), (-7, 0, -2, 0), # Letter H
    (1, -6, 1, 6), (1, -6, 6, -6), (1, 0, 5, 0), (1, 6, 6, 6), # Letter E
    (9, -6, 9, 6), (9, -6, 14, -6), (14, -6, 14, 0), (9, 0, 14, 0), (9, 0, 14, 6), # Letter R
    (17, -6, 17, 6), (22, -6, 22, 6), (17, -6, 22, -6), (17, 6, 22, 6), (22, -6, 17, 6), # Number 0 (with slash)
    (25, -6, 25, 6), (30, -6, 30, 6), (25, -6, 30, -6), (25, 6, 30, 6), (30, -6, 25, 6), # Number 0 (with slash)
    (33, -6, 38, -6), (33, -6, 33, 6), (33, 6, 38, 6), (38, 0, 38, 6), (33, 0, 38, 0) # Number 6
] # End of custom text list

GRAVITY = 0.08 # Define downward acceleration added to snow every single frame
FRICTION = 0.95 # Define damping factor to slow down snow sliding on the logo
MAX_SNOW = 10 # HARD CAP: Reduced to 10 massive falling snowflakes maximum
MAX_PILE = 200 # Set a hard cap on maximum accumulated snow pixels on the logo
ROT_STEPS = 126 # Define the number of steps in our 360 degree rotation (approx 2pi / 0.05)
MELT_RATE = 60 # Set to 60 frames so the snow takes a few seconds to melt away

# --- RAM FOR SPEED: PRE-COMPUTED TRIGONOMETRY LOOKUP TABLES (LUT) ---
SIN_LUT = [0.0] * ROT_STEPS # Allocate an array for 126 pre-calculated sine values
COS_LUT = [0.0] * ROT_STEPS # Allocate an array for 126 pre-calculated cosine values
for i in range(ROT_STEPS): # Loop through all possible rotation steps
    angle = i * 0.05 # Calculate the actual radian angle for this step
    SIN_LUT[i] = math.sin(angle) # Calculate and store the sine value permanently
    COS_LUT[i] = math.cos(angle) # Calculate and store the cosine value permanently

# --- TRUE ZERO ALLOCATION: SHARED VECTORS & PARALLEL ARRAYS ---
state = {} # Initialize an empty global dictionary to hold the application state
box_pts = [] # Flat list to hold pre-calculated local X,Y coordinates for the blue box
text_pts = [] # Flat list to hold pre-calculated local X,Y coordinates for the cyan text
v_pixel = Vector(0, 0) # Pre-allocate a shared Vector for drawing individual pixels
v_pos = Vector(0, 0) # Pre-allocate a shared Vector for UI text and rect positioning
v_size = Vector(0, 0) # Pre-allocate a shared Vector for dynamic rect sizing
v_flake = Vector(4, 4) # INCREASED: Pre-allocate a fixed Vector for much larger 4x4 snowflake sizes

# Parallel arrays for SNOW (Eliminates dictionary hash lookups)
sn_act = [False] * MAX_SNOW # Array tracking if snowflake index is currently active
sn_x = [0.0] * MAX_SNOW # Array tracking X coordinate of each snowflake
sn_y = [0.0] * MAX_SNOW # Array tracking Y coordinate of each snowflake
sn_vx = [0.0] * MAX_SNOW # Array tracking X velocity of each snowflake
sn_vy = [0.0] * MAX_SNOW # Array tracking Y velocity of each snowflake
sn_px = [0.0] * MAX_SNOW # Array tracking previous X coordinate of each snowflake
sn_py = [0.0] * MAX_SNOW # Array tracking previous Y coordinate of each snowflake

# Parallel arrays for PILE (Eliminates dictionary hash lookups)
pl_act = [False] * MAX_PILE # Array tracking if pile pixel index is currently active
pl_rx = [0.0] * MAX_PILE # Array tracking relative X coordinate of each pile pixel
pl_ry = [0.0] * MAX_PILE # Array tracking relative Y coordinate of each pile pixel
pl_sv = [0.0] * MAX_PILE # Array tracking sliding velocity of each pile pixel
pl_edge = [0] * MAX_PILE # Array tracking which edge the pixel is on (0=Top, 1=Bot, 2=Left, 3=Right)

def cache_line(pts_list, x0, y0, x1, y1): # Function to pre-compute Bresenham line pixels ONCE
    x0, y0, x1, y1 = int(x0), int(y0), int(x1), int(y1) # Ensure coordinates are integers
    dx = abs(x1 - x0) # Calculate absolute horizontal distance
    sx = 1 if x0 < x1 else -1 # Determine horizontal step direction
    dy = -abs(y1 - y0) # Calculate absolute vertical distance
    sy = 1 if y0 < y1 else -1 # Determine vertical step direction
    err = dx + dy # Initialize the mathematical error term
    while True: # Begin pixel plotting loop
        pts_list.append(x0) # Append the X coordinate sequentially to the flat list
        pts_list.append(y0) # Append the Y coordinate sequentially to the flat list
        if x0 == x1 and y0 == y1: break # Exit when endpoint is reached
        e2 = 2 * err # Calculate double error
        if e2 >= dy: # Evaluate X shift
            err += dy # Adjust error
            x0 += sx # Shift X
        if e2 <= dx: # Evaluate Y shift
            err += dx # Adjust error
            y0 += sy # Shift Y

def start(view_manager): # Lifecycle function called when the app starts or resets
    global SCREEN_W, SCREEN_H, CX, CY, GROUND_CHUNKS # Declare globals to modify them dynamically
    SCREEN_W = view_manager.draw.size.x # Ask the hardware for the exact full screen width
    SCREEN_H = view_manager.draw.size.y # Ask the hardware for the exact full screen height
    CX = SCREEN_W // 2 # Mathematically calculate the exact horizontal center
    CY = SCREEN_H // 2 # Mathematically calculate the exact vertical center
    GROUND_CHUNKS = (SCREEN_W // 4) + 1 # Calculate exact number of 4-pixel chunks needed to span the full screen
    
    state["stage"] = 0 # Set stage to 0 for the initial waiting period
    state["start_time"] = time.ticks_ms() # Record the exact millisecond the app launched
    state["a_idx"] = 0 # Reset the logo rotation index to 0 (flat)
    state["rot"] = False # Ensure rotation is paused when the app starts
    state["ground"] = [SCREEN_H] * GROUND_CHUNKS # Initialize the ground chunks array mapping the full screen width
    state["tick"] = 0 # Initialize a frame counter for the melting optimization
    
    for i in range(MAX_SNOW): sn_act[i] = False # Hard reset all snowflakes to dormant
    for i in range(MAX_PILE): pl_act[i] = False # Hard reset all pile pixels to dormant
    box_pts.clear() # Empty the global point cloud cache for the box
    text_pts.clear() # Empty the global point cloud cache for the text
    
    cache_line(box_pts, L_LEFT, L_TOP, L_RIGHT, L_TOP) # Cache top edge of logo
    cache_line(box_pts, L_RIGHT, L_TOP, L_RIGHT, L_BOT) # Cache right edge of logo
    cache_line(box_pts, L_RIGHT, L_BOT, L_LEFT, L_BOT) # Cache bottom edge of logo
    cache_line(box_pts, L_LEFT, L_BOT, L_LEFT, L_TOP) # Cache left edge of logo
    for line in LOGO_LINES: # Iterate through all "Slasher006" text segments
        cache_line(text_pts, line[0], line[1], line[2], line[3]) # Cache the text pixels
        
    view_manager.draw.fill_screen(TFT_BLACK) # Clear the entire screen to black
    view_manager.draw.swap() # Push the black frame to the physical display
    return True # Return true to tell the framework initialization succeeded

def run(view_manager): # Lifecycle function called every single frame
    draw = view_manager.draw # Create a local reference to the drawing API
    input_mgr = view_manager.input_manager # Create a local reference to the input API
    button = input_mgr.button # Cache the current active physical button press state
    now = time.ticks_ms() # Get the current system time in milliseconds
    
    # --- FUNCTION CACHING FOR EXTREME LOOP SPEED ---
    _int = int # Cache the integer cast function locally
    _abs = abs # Cache the absolute value function locally
    _min = min # Cache the minimum value function locally
    _rand = random.random # Cache the random float generator locally
    _rand_r = random.randrange # Cache the random integer generator locally
    _rand_u = random.uniform # Cache the random uniform generator locally
    
    # --- VARIABLE CACHING FOR EXTREME LOOP SPEED ---
    _scr_w = SCREEN_W # Cache the dynamic screen width locally
    _scr_h = SCREEN_H # Cache the dynamic screen height locally
    _cx = CX # Cache the dynamic horizontal center locally
    _cy = CY # Cache the dynamic vertical center locally
    _g_chunks = GROUND_CHUNKS # Cache the dynamic ground chunk count locally
    
    # --- INPUT HANDLING ---
    if button == BUTTON_BACK or button == BUTTON_ESCAPE: # Check if the user pressed the back OR escape button
        input_mgr.reset() # Clear the button press state from the input manager
        view_manager.back() # Command the view manager to cleanly exit this application
        return # Halt execution of the current frame immediately
    if button == BUTTON_G and state["stage"] == 1: # Check if 'g' was pressed during active stage
        state["rot"] = not state["rot"] # Toggle the boolean rotation state (Play/Pause)
        input_mgr.reset() # Clear the button press state
    if button == BUTTON_R: # Check if 'r' was pressed at any time
        start(view_manager) # Call the start function to trigger a hard reset
        input_mgr.reset() # Clear the button press state
        return # Halt execution to start fresh on the next tick

    if state["stage"] == 0 and time.ticks_diff(now, state["start_time"]) > 5000: # Check wait phase timer
        state["stage"] = 1 # Advance to the active snowing phase
            
    a_idx = state["a_idx"] # Pull the current angle index into a fast local variable
    s_ang = SIN_LUT[a_idx] # Instantly lookup the sine value from RAM without math
    c_ang = COS_LUT[a_idx] # Instantly lookup the cosine value from RAM without math
            
    if state["stage"] == 1: # Check if the application is fully active
        state["tick"] += 1 # Increment the global frame counter
        
        # --- MELTING OPTIMIZATION LOGIC ---
        if state["tick"] % MELT_RATE == 0: # Check if it is time to melt the snow based on the delayed MELT_RATE
            for i in range(_g_chunks): # Iterate through all available dynamic ground chunks
                if state["ground"][i] < _scr_h: # If there is snow piled up in this chunk above the floor
                    state["ground"][i] += 1 # Melt it by pushing the top Y coordinate down 1 pixel towards the floor
        
        if _rand() < 0.4: # Spawning check: 40% chance per frame using cached random
            for i in range(MAX_SNOW): # Loop through snowflake pool indices
                if not sn_act[i]: # Find first dormant snowflake
                    sn_act[i] = True # Wake it up
                    sn_x[i] = _rand_r(0, _scr_w) # Assign random X spanning the entire dynamic width
                    sn_y[i] = -5.0 # Assign Y above screen
                    sn_vx[i] = _rand_u(-0.3, 0.3) # Assign wind drift
                    sn_vy[i] = _rand_u(0.5, 1.5) # Assign fall speed
                    sn_px[i] = sn_x[i] # Init previous X
                    sn_py[i] = sn_y[i] # Init previous Y
                    break # Break loop after spawning one
            
        if state["rot"]: # If rotation is active
            state["a_idx"] = (a_idx + 1) % ROT_STEPS # Increment angle index and wrap around lookup table
            
        for i in range(MAX_SNOW): # Loop through all snowflake indices
            if not sn_act[i]: continue # Skip dormant snowflakes instantly
            
            x = sn_x[i] # Load X to local register
            y = sn_y[i] # Load Y to local register
            sn_px[i] = x # Store as previous X
            sn_py[i] = y # Store as previous Y
            
            vy = sn_vy[i] + GRAVITY # Calculate new Y velocity
            sn_vy[i] = vy # Save new Y velocity
            x += sn_vx[i] # Apply X velocity
            y += vy # Apply Y velocity
            sn_x[i] = x # Save new X position
            sn_y[i] = y # Save new Y position
            
            landed = False # Initialize landing flag
            chunk = _int(x) >> 2 # BITWISE MATH: Divide X by 4 to find ground chunk mapping
            
            if 0 <= chunk < _g_chunks: # Ensure chunk mapping is within the dynamic screen bounds
                if y + 4 >= state["ground"][chunk]: # Check ground collision adjusted for the larger 4x4 size
                    state["ground"][chunk] -= 4 # Raise ground level locally by 4 pixels to match the big flake
                    landed = True # Mark as landed
                    
            if not landed: # Check logo collision
                dx = x - _cx # Translate to local X using cached dynamic center
                dy = y - _cy # Translate to local Y using cached dynamic center
                lx = dx * c_ang + dy * s_ang # INLINE MATH: Inverse rotate X
                ly = -dx * s_ang + dy * c_ang # INLINE MATH: Inverse rotate Y
                
                if L_LEFT <= lx <= L_RIGHT and L_TOP <= ly <= L_BOT: # Check bounding box
                    dt = _abs(ly - L_TOP) # Dist to top
                    db = _abs(ly - L_BOT) # Dist to bot
                    dl = _abs(lx - L_LEFT) # Dist to left
                    dr = _abs(lx - L_RIGHT) # Dist to right
                    m = _min(dt, db, dl, dr) # Find closest edge
                    
                    for p in range(MAX_PILE): # Find available pile pixel
                        if not pl_act[p]: # If dormant
                            pl_act[p] = True # Wake up
                            pl_sv[p] = 0.0 # Reset sliding
                            if m == dt: # Top edge
                                pl_rx[p], pl_ry[p], pl_edge[p] = lx, L_TOP, 0 # Snap to top
                            elif m == db: # Bot edge
                                pl_rx[p], pl_ry[p], pl_edge[p] = lx, L_BOT, 1 # Snap to bot
                            elif m == dl: # Left edge
                                pl_rx[p], pl_ry[p], pl_edge[p] = L_LEFT, ly, 2 # Snap to left
                            else: # Right edge
                                pl_rx[p], pl_ry[p], pl_edge[p] = L_RIGHT, ly, 3 # Snap to right
                            break # End pile search
                    landed = True # Mark as landed
                        
            if landed or y >= _scr_h: # If it hit something or fell completely past the dynamic screen height
                sn_act[i] = False # Put snowflake back to sleep

        gx = s_ang * GRAVITY * 2.0 # X gravity along horizontal edges
        gy = c_ang * GRAVITY * 2.0 # Y gravity along vertical edges
        
        for p in range(MAX_PILE): # Loop through pile pixels
            if not pl_act[p]: continue # Skip dormant pixels
            
            e = pl_edge[p] # Load edge ID (0=T, 1=B, 2=L, 3=R)
            fall = False # Init fall flag
            sv = pl_sv[p] # Load sliding velocity
            
            if e == 0: # Top Edge
                if gy < 0: fall = True # Upside down, fall off
                else: # Sliding
                    sv = (sv + gx) * FRICTION # Accelerate and apply friction
                    rx = pl_rx[p] + sv # Update relative X
                    pl_rx[p] = rx # Save relative X
                    if rx < L_LEFT or rx > L_RIGHT: fall = True # Check ends
            elif e == 1: # Bot Edge
                if gy > 0: fall = True # Upside down, fall off
                else: # Sliding
                    sv = (sv + gx) * FRICTION # Accelerate and apply friction
                    rx = pl_rx[p] + sv # Update relative X
                    pl_rx[p] = rx # Save relative X
                    if rx < L_LEFT or rx > L_RIGHT: fall = True # Check ends
            elif e == 2: # Left Edge
                if gx > 0: fall = True # Sideways, fall off
                else: # Sliding
                    sv = (sv + gy) * FRICTION # Accelerate and apply friction
                    ry = pl_ry[p] + sv # Update relative Y
                    pl_ry[p] = ry # Save relative Y
                    if ry < L_TOP or ry > L_BOT: fall = True # Check ends
            elif e == 3: # Right Edge
                if gx < 0: fall = True # Sideways, fall off
                else: # Sliding
                    sv = (sv + gy) * FRICTION # Accelerate and apply friction
                    ry = pl_ry[p] + sv # Update relative Y
                    pl_ry[p] = ry # Save relative Y
                    if ry < L_TOP or ry > L_BOT: fall = True # Check ends
            
            pl_sv[p] = sv # Save updated velocity
            
            if fall: # If slid off the edge
                pl_act[p] = False # Sleep pixel
                rx = pl_rx[p] # Load local X
                ry = pl_ry[p] # Load local Y
                ax = rx * c_ang - ry * s_ang + _cx # Convert to absolute X using dynamic center
                ay = rx * s_ang + ry * c_ang + _cy # Convert to absolute Y using dynamic center
                if e < 2: # Horizontal edge falling momentum
                    vx, vy = sv * c_ang, sv * s_ang + 1.0 # Calc trajectories
                else: # Vertical edge falling momentum
                    vx, vy = -sv * s_ang, sv * c_ang + 1.0 # Calc trajectories
                    
                for i in range(MAX_SNOW): # Re-add to falling pool
                    if not sn_act[i]: # Find dormant flake
                        sn_act[i] = True # Wake up
                        sn_x[i], sn_y[i] = ax, ay # Assign position
                        sn_px[i], sn_py[i] = ax, ay # Assign prev position
                        sn_vx[i], sn_vy[i] = vx, vy # Assign velocities
                        break # Stop looking

    draw.fill_screen(TFT_BLACK) # Wipe screen
    dp = draw.pixel # Cache drawing method
    dr = draw.rect # Cache drawing method
    
    for i in range(_g_chunks): # Render Ground chunks spanning full dynamic width
        y_top = state["ground"][i] # Extract top Y
        if y_top < _scr_h: # If accumulated above dynamic screen height
            v_pos.x = i << 2 # BITWISE MATH: i * 4
            v_pos.y = y_top # Set Y
            v_size.x = 4 # Set Width
            v_size.y = _scr_h - y_top # Set Height dynamically to reach the floor
            dr(v_pos, v_size, TFT_WHITE) # Draw chunk
            
    for i in range(MAX_SNOW): # Render Falling Snow
        if sn_act[i]: # If active
            v_pos.x = _int(sn_x[i]) # Set X
            v_pos.y = _int(sn_y[i]) # Set Y
            dr(v_pos, v_flake, TFT_WHITE) # Draw the large 4x4 flake
            
    for i in range(0, len(box_pts), 2): # Render Box Point Cloud
        px, py = box_pts[i], box_pts[i+1] # Load local coords
        v_pixel.x = _int(px * c_ang - py * s_ang) + _cx # Rotate X using dynamic center
        v_pixel.y = _int(px * s_ang + py * c_ang) + _cy # Rotate Y using dynamic center
        dp(v_pixel, TFT_BLUE) # Draw blue pixel
        
    for i in range(0, len(text_pts), 2): # Render Text Point Cloud
        px, py = text_pts[i], text_pts[i+1] # Load local coords
        v_pixel.x = _int(px * c_ang - py * s_ang) + _cx # Rotate X using dynamic center
        v_pixel.y = _int(px * s_ang + py * c_ang) + _cy # Rotate Y using dynamic center
        dp(v_pixel, TFT_CYAN) # Draw cyan pixel

    for i in range(MAX_PILE): # Render Logo Pile
        if pl_act[i]: # If active
            px, py = pl_rx[i], pl_ry[i] # Load relative coords
            v_pixel.x = _int(px * c_ang - py * s_ang) + _cx # Rotate X using dynamic center
            v_pixel.y = _int(px * s_ang + py * c_ang) + _cy # Rotate Y using dynamic center
            dp(v_pixel, TFT_WHITE) # Draw pile pixel

    if state["stage"] == 0: # Render UI Phase 0
        v_pos.x = 10 # Set UI X
        v_pos.y = 10 # Set UI Y
        draw.text(v_pos, "WAIT 5 SECONDS...", TFT_YELLOW) # Draw text updates help screen dynamically
        v_pos.y = 25 # Move UI Y down for the next line
        draw.text(v_pos, "[ESC]: EXIT", TFT_YELLOW) # Draw explicit escape instruction
    elif state["stage"] == 1: # Render UI Phase 1
        rot_status = "PAUSED" if not state["rot"] else "ROTATING" # Conditional string
        v_pos.x = 5 # Set UI X
        v_pos.y = 5 # Set UI Y
        draw.text(v_pos, f"[G]: {rot_status}", TFT_YELLOW) # Draw toggle text updates help screen dynamically
        v_pos.y = 20 # Move UI Y
        draw.text(v_pos, "[R]: RESET", TFT_YELLOW) # Draw reset text updates help screen dynamically
        v_pos.y = 35 # Move UI Y down for the next line
        draw.text(v_pos, "[ESC]: EXIT", TFT_YELLOW) # Draw explicit escape instruction

    draw.swap() # Push final frame to display

def stop(view_manager): # Cleanup on exit
    import gc # Import garbage collector
    box_pts.clear() # Clear box memory
    text_pts.clear() # Clear text memory
    gc.collect() # Force memory reclaim
