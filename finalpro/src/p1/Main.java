package p1;

import javafx.application.Application;
import javafx.stage.Stage;

/**
 * Main class of the game.
 *
 * @author Hanwu Zhou
 */
public class Main extends Application {

    private Stage primaryStage; // The primary stage of the game.

    public static void main(String[] args) {
        launch(args);
    }

    @Override
    public void start(Stage primaryStage) {

        this.primaryStage = primaryStage;
        // Create a new game.
        new_game();

        primaryStage.setTitle("Game");
        primaryStage.show();
    }

    /**
     * Create a new game.
     */
    public void new_game(){
        // The current game.
        Game game = new Game(this);
        primaryStage.setScene(game.getScene());
    }
}
