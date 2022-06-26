package p1;

import javafx.scene.image.Image;

/**
 * Bullet class
 * @author Hanwu Zhou
 */
public class Bullet extends Skillshots{

    private final static Image image = new Image("images/bullet.png"); // The image of the bullet.
    private final static int damage = 5; // The damage of the bullet.
    /**
     * Constructor of the bullet.
     *
     * @param target the target of the bullet.
     * @param game the game the bullet belongs to.
     * @param speed the speed of the bullet.
     */
    public Bullet(Character target, Game game, int speed){
        super(target, game, image, damage, speed);
    }
}

