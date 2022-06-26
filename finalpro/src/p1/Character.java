package p1;

import javafx.geometry.Bounds;
import javafx.geometry.Point2D;
import javafx.scene.Group;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.paint.Color;
import javafx.scene.shape.Circle;
import javafx.scene.shape.Rectangle;

/**
 * Main character class
 * @author Hanwu Zhou
 */
public class Character {
    private final static Image image = new Image("images/player.png"); // The image of the character.
    private Rectangle HPBar; // The HP bar of the character.
    private int hp = 100; // The current HP of the character.
    private int maxHP = 100; // The max HP of the character.
    private int speed = 5; // The speed of the character.
    private Group player; // A player consists of different components, including the imageview and the hit box. Other things could be added as well.
    private Point2D path; // The path to move, set by the mouse position.
    private Point2D up; // The up direction of the character.
    private double x, y; // The current position of the character.
    private double rotation; // The rotation of the character.
    private Game game; // The game the character belongs to.
    private double va; // angular velocity of the character.
    private double dist; // The distance to the target position.

    private Circle center; // The center of the character, also the hit box.

    /**
     * Constructor of the character.
     * @param game the game the character belongs to.
     */
    public Character(Game game){
        this.game = game;

        // Create a group for the character.
        player = new Group();
        player.getChildren().add(new ImageView(image));

        // Calculate the center of the character.
        Bounds b = player.getBoundsInParent();
        x = (b.getMaxX()+b.getMinX())/2;
        y = (b.getMaxY()+b.getMinY())/2;

        // The image faces up by default.
        up = new Point2D(0,-1);

        // Create a hit box for the character.
        center = new Circle(x, y, 10);
        center.setFill(Color.TRANSPARENT);
        player.getChildren().add(center);

        // Translate the player to the center of the screen.
        player.setTranslateX(Game.WIDTH/2-x);
        player.setTranslateY(Game.HEIGHT/2-y);
        x += Game.WIDTH/2-x;
        y += Game.HEIGHT/2-y;

        // Create a HP bar for the character.
        Rectangle HPFrame = new Rectangle(Game.WIDTH/2-252, Game.HEIGHT-22, 504, 14);
        HPFrame.setOpacity(0.5);
        game.add(HPFrame);
        HPBar = new Rectangle(Game.WIDTH/2-250, Game.HEIGHT-20, hp*500/maxHP, 10);
        HPBar.setFill(Color.RED);
        HPBar.setOpacity(0.5);

        game.add(player);
        game.add(HPBar);
    }

    /**
     * Move the character to the target position each frame.
     */
    public void mouse_move(){
        if(path!=null) {
            // rotate the character to face the target position first if the character is not facing the target position, then move the character to the target position.
            if (rotation!=0 && Math.abs(rotation) > Math.abs(va)) {
                player.setRotate(player.getRotate() + va);
                rotation -= va;
                up = new Point2D(Math.cos(Math.toRadians(-player.getRotate()+90)), -Math.sin(Math.toRadians(-player.getRotate()+90)));
            } else if(rotation!=0){
                player.setRotate(player.getRotate() + rotation);
                rotation = 0;
                up = new Point2D(Math.cos(Math.toRadians(-player.getRotate()+90)), -Math.sin(Math.toRadians(-player.getRotate()+90)));
            }else if(dist>speed){
                player.setTranslateX(player.getTranslateX() + up.getX() * speed);
                player.setTranslateY(player.getTranslateY() + up.getY() * speed);
                x += up.getX() * speed;
                y += up.getY() * speed;
                dist -= speed;
            }else{
                player.setTranslateX(player.getTranslateX() + up.getX() * dist);
                player.setTranslateY(player.getTranslateY() + up.getY() * dist);
                x += up.getX() * dist;
                y += up.getY() * dist;
                dist = 0;
                path = null;
            }
        }
    }

    /**
     * Set the path to move.
     * @param x the x coordinate of the target position.
     * @param y the y coordinate of the target position.
     */
    public void set_target(double x, double y){
        if(x != this.x && y != this.y) {
            path = new Point2D(x - this.x, y - this.y); // the path to follow
            rotation = up.crossProduct(path).getZ() >= 0 ? path.angle(up) : -path.angle(up); // angle to rotate
            dist = path.magnitude(); // distance to travel
            if (rotation != 0)
                va = rotation / Math.abs(rotation) * 5 * speed; // angular velocity
        }
    }

    /**
     * Accelerate the character.
     */
    public void speedUp(){
        speed+=2;
    }

    /**
     * Get the x coordinate of the character.
     * @return x coordinate of the character.
     */
    public double getX(){
        return x;
    }

    /**
     * Get the y coordinate of the character.
     * @return  y coordinate of the character.
     */
    public double getY(){
        return y;
    }

    /**
     * Get the hit box of the character.
     * @return the hit box of the character.
     */
    public Bounds getBoundsInParent() {
        return player.localToParent(center.getBoundsInLocal());
    }

    /**
     * Decrease the HP of the character, and update the HP bar.
     * @param dmg the damage received.
     */
    public void decrease_health(int dmg){
        hp -= dmg;
        HPBar.setWidth(hp*500/maxHP);
        // if the HP is 0, the character is dead, game is over.
        if(hp <= 0){
            game.game_over();
        }
    }
}
