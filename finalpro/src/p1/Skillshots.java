package p1;

import javafx.geometry.Point2D;
import javafx.scene.Node;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;

import java.util.Random;

/**
 * A skillshot is a projectile that randomly spawn outside the scene and move towards the target.
 *
 * @author Hanwu Zhou
 */
public class Skillshots {
    private Character target; // The target of the skillshot.
    private ImageView imageView; // The image view of the skillshot.
    private Point2D path; // The path to follow the target.
    private double speed; // The speed of the skillshot.
    private double x, y; // The current position of the skillshot.
    private int damage; // The damage the skillshot can deal.
    private Game game; // The game the skillshot belongs to.

    /**
     * Constructor of the skillshot.
     *
     * @param target the main character of the game.
     * @param game the game the skillshot belongs to.
     * @param image the image of the skillshot.
     * @param damage the damage the skillshot can deal.
     * @param speed the speed of the skillshot.
     */
    public Skillshots(Character target, Game game, Image image, int damage, int speed){
        imageView = new ImageView(image);
        this.target = target;
        this.speed = speed;
        this.damage = damage;
        this.game = game;
        // The width and height of the skillshot.
        double width = image.getWidth();
        double height = image.getHeight();
        // Randomly spawn the skillshot at the edge of the scene.
        Random r = new Random();
        switch (r.nextInt(4)){
            case 0:
                // top
                x = r.nextInt(Game.WIDTH);
                y = -height *3;
                break;
            case 1:
                // right
                x = Game.WIDTH + width;
                y = r.nextInt(Game.HEIGHT);
                break;
            case 2:
                // bottom
                x = r.nextInt(Game.WIDTH);
                y = Game.HEIGHT + height;
                break;
            case 3:
                // left
                x = -width;
                y = r.nextInt(Game.HEIGHT);
                break;
        }
        imageView.setX(x- width /2);
        imageView.setY(y);

        // calculate the direction the skillshot should move, path is a unit vector
        double x1 = x - target.getX();
        double y1 = y - target.getY();
        path = new Point2D(x1, y1);
        path = path.normalize();

        // rotate or flip the image so that it faces the target.
        if(x1 < 0){
            imageView.setScaleY(-1);
        }
        imageView.setRotate(Math.toDegrees(Math.atan2(y1, x1)));

        game.add(imageView);
    }

    /**
     * Update the position of the skillshot, get called every frame.
     */
    public void fire(){
        // if the skillshot is out of the scene, remove it.
        if(imageView.getX() < -Game.WIDTH || imageView.getX() > 2*Game.WIDTH || imageView.getY() < -Game.HEIGHT || imageView.getY() > 2*Game.HEIGHT){
            this.destroy();
            return;
        }
        // move the skillshot towards the target.
        imageView.setX(imageView.getX() - path.getX()*speed);
        imageView.setY(imageView.getY() - path.getY()*speed);
        // if the skillshot hits the target, deal damage to the target.
        if(imageView.getBoundsInParent().intersects(target.getBoundsInParent())){
            target.decrease_health(damage);
            game.remove(this);
        }
    }

    /**
     * Remove the skillshot from the game.
     */
    public void destroy(){
        game.remove(this);
    }

    /**
     * Get the image view of the skillshot.
     *
     * @return the image view of the skillshot.
     */
    public Node getNode(){
        return imageView;
    }
}
