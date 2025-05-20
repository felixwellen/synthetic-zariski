# created using machine intelligence

plane = implicit_plot3d(
    lambda x, y, z: x - 1,  # Equation x = 1
    (0.8, 1.2),             # x-range close to x=1 (to make it visible)
    (-1.7, 1.7),                # y-range
    (-1.7, 1.7),                # z-range
    color='lightblue',
    opacity=0.8
)

plane.show(aspect_ratio=1)
# Define axes with arrow tips
x_arrow = arrow3d((0, 0, 0), (2, 0, 0), color='black', width=1)
y_arrow = arrow3d((0, 0, 0), (0, 2, 0), color='black', width=1)
z_arrow = arrow3d((0, 0, 0), (0, 0, 2), color='black', width=1)

# Add labels near tips
x_label = text3d("x", (2.2, 0, 0), color='black')
y_label = text3d("y", (0, 2.2, 0), color='black')
z_label = text3d("z", (0, 0, 2.2), color='black')

# Combine all
axes = x_arrow + y_arrow + z_arrow + x_label + y_label + z_label

# Direction vector of the line (non-zero vector through the origin)

# Parametric plot of the line: t * v for t in [-1.5, 1.5]
def L_x(t):
    return t
def L_y(t):
    return 0.6*t
def L_z(t):
    return 0.5*t

line = parametric_plot3d(
    [L_x,L_y,L_z],
    (t, -1.5, 1.5),
    color='red',
    thickness=4    
)

scene = plane + axes + line
scene.show(aspect_ratio=1, frame=False)
