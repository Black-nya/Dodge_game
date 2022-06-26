package p1;

import javafx.scene.image.Image;

/**
 * Bird class
 * @author Hanwu Zhou
 */
public class Bird extends Skillshots{
    private final static Image image = new Image("images/bird.png"); // The image of the bird.
    private final static int damage = 10; // The damage of the bird.

    /**
     * Constructor of the bird.
     * @param target the target of the bird.
     * @param game  the game the bird belongs to.
     * @param speed the speed of the bird.
     */
    public Bird(Character target, Game game, int speed){
        super(target, game, image, damage, speed);
    }
}
