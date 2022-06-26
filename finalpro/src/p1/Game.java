package p1;

import javafx.animation.Animation;
import javafx.animation.AnimationTimer;
import javafx.animation.KeyFrame;
import javafx.animation.Timeline;
import javafx.collections.ObservableList;
import javafx.scene.Group;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.input.MouseButton;
import javafx.scene.paint.Color;
import javafx.scene.shape.Rectangle;
import javafx.scene.text.Font;
import javafx.scene.text.Text;
import javafx.util.Duration;
import javafx.util.Pair;
import java.io.*;
import java.util.ArrayList;

/**
 * The game class
 *
 * @author Hanwu Zhou
 */
public class Game {

    public static final int WIDTH = 1600; // width of the game
    public static final int HEIGHT = 900; // height of the game
    private ObservableList<Node> list; //list of all nodes in the scene
    private Scene scene; // scene of the game
    private Character chara; // main character of the game
    private ArrayList<Skillshots> skillshots; // list of all projectiles in the game
    private long last1; // timer for spawning bullets
    private long last2; // timer for spawning birds
    private long last3; // timer for controlling the frame rate
    private Timeline timer; // timer for how long the player last
    private int seconds, minutes; // time past since the start of the game
    private AnimationTimer at; // animation timer for the game
    private boolean isPaused; // whether the game is paused
    private Text score; // text for display the current score
    private int speed; // the speed of the game
    private int frame_rate;
    private Main main; // the main class
    private String font = "file:src/font/Fresh_Lychee.ttf"; // font of the game
    private ImageView pause_screen; // pause screen of the game
    private Image pause_normal = new Image("file:src/images/pause_nor.png"); // normal image of the pause button
    private Image pause_hover = new Image("file:src/images/pause_hov.png"); // hover image of the pause button
    private Image resume_normal = new Image("file:src/images/resume_nor.png"); // normal image of the resume button
    private Image resume_hover = new Image("file:src/images/resume_hov.png"); // hover image of the resume button
    private int nextLetter = 0; // the next letter to be displayed, used for game over text display
    private Image background_image = new Image("file:src/images/background.jpeg"); // background image of the game
    private Image restart_normal = new Image("file:src/images/restart.png"); // normal image of the restart button
    private Image restart_hover = new Image("file:src/images/restart_hov.png"); // hover image of the restart button
    public Game(Main main){

        this.main = main;
        // create a root for the scene
        Group root = new Group();
        // create a scene under the root
        scene = new Scene(root, 1600, 900);
        // get the list that stores all nodes in the scene
        list = root.getChildren();

        // set the background of the game
        ImageView background = new ImageView(background_image);
        pause_screen = new ImageView(background_image);
        list.add(background);

        // create a main character
        chara = new Character(this);
        // set the initial speed of the game
        speed = 2;
        // create a list for storing all projectiles
        skillshots = new ArrayList<>();

        // initialize the timers to 0
        last1 = last2 = last3 = 0;


        // create the text for display the current time, which is the player's score
        score = new Text(WIDTH/2-30, 35, "00:00");
        score.setFont(Font.loadFont( font,50));
        list.add(score);

        // initialize the time to 0
        seconds = minutes = 0;
        // update the time every second if the game is not paused
        timer = new Timeline(new KeyFrame(Duration.seconds(1), event -> {
            if(!isPaused) {
                seconds++;
                // every 15 seconds, the speed of the game increases
                if(seconds % 15 == 0){
                    if(speed <= 10) {
                        chara.speedUp();
                        speed += 2;
                    }
                }
                // every 60 seconds is 1 minute
                if(seconds == 60){
                    seconds = 0;
                    minutes++;
                }
                // update the text for display the current time
                score.setText(String.format("%02d:%02d", minutes, seconds));
            }
        }));
        timer.setCycleCount(Animation.INDEFINITE);
        timer.play();
        // sets the frame_rate of the game
        frame_rate = 100;
        // create an animation timer for the game
        at = new AnimationTimer() {
            @Override
            public void handle(long now) {
                // spawn 5 bullets every second
                if(now - last1 > 1e9/5){
                    skillshots.add(new Bullet(chara, Game.this, speed+3));
                    last1 = now;
                }
                // spawn 2 birds every second
                if(now - last2 > 1e9/2){
                    skillshots.add(new Bird(chara, Game.this, speed));
                    last2 = now;
                }
                // update the position of all projectiles and character every frame
                if(now - last3 > 1e9/frame_rate) {
                    chara.mouse_move();
                    ArrayList<Skillshots> copy = (ArrayList<Skillshots>) skillshots.clone();
                    for (Skillshots s : copy) {
                        s.fire();
                    }
                    last3 = now;
                }
            }
        };
        at.start();
        // game is not paused by default
        isPaused = false;

        // create a button for pause the game
        ImageView pause = new ImageView(pause_normal);
        pause.setX(WIDTH-pause.getImage().getWidth());
        pause.setY(10);
        pause.setOnMouseEntered(event -> {
            if(!isPaused)
                pause.setImage(pause_hover);
            else
                pause.setImage(resume_hover);
        });
        pause.setOnMouseExited(event -> {
            if(!isPaused)
                pause.setImage(pause_normal);
            else
                pause.setImage(resume_normal);
        });
        pause.setOnMouseClicked(event -> {
            if(!isPaused) {
                pause.setImage(resume_hover);
                at.stop();
                timer.pause();
                isPaused = true;
                list.add(pause_screen);
                pause.toFront();
            }else{
                pause.setImage(pause_hover);
                at.start();
                timer.play();
                isPaused = false;
                list.remove(pause_screen);
            }
        });
        list.add(pause);

        // set the target position for main character after right-click
        scene.setOnMouseClicked(event ->{
            if(event.getButton() == MouseButton.SECONDARY){
                chara.set_target(event.getX(), event.getY());
            }
        });

    }

    /**
     * get the scene of the game
     * @return the scene of the game
     */
    public Scene getScene(){
        return scene;
    }

    /**
     * Add a node to the scene
     * @param e node to be added
     */
    public void add(Node e){
        list.add(e);
    }

    /**
     * Remove a projectile from the scene
     * @param s projectile to be removed
     */
    public void remove(Skillshots s){
        skillshots.remove(s);
        list.remove(s.getNode());
    }

    /**
     * game over screen
     */
    public void game_over(){
        // stop the game
        at.stop();
        timer.stop();

        // Create a game over screen
        ImageView rect = new ImageView(background_image);
        list.add(rect);

        // Create a gradually appearing text for game over and scores
        String txt = "Game Over";
        Text text = new Text(WIDTH/2-130, HEIGHT/2-100, "");
        text.setFill(Color.WHITE);
        text.setFont(Font.loadFont(font, 80));
        Timeline timeline = new Timeline(new KeyFrame(Duration.seconds(1.0/txt.length()), event -> {
            text.setText(text.getText() + txt.charAt(nextLetter));
            nextLetter++;
        }));
        timeline.setCycleCount(txt.length());
        timeline.play();

        Pair<Integer, Integer> record = read();
        if(minutes*60+seconds > record.getKey()*60+record.getValue()){
            record();
        }
        String score_txt = "Highest score: " + String.format("%02d:%02d", record.getKey(), record.getValue()) + "\nYour score: " + String.format("%02d:%02d", minutes, seconds);
        //System.out.println(score_txt);
        Text score_text = new Text(WIDTH/2-125, HEIGHT/2-50, "");
        score_text.setFill(Color.WHITE);
        score_text.setFont(Font.loadFont(font, 40));

        // Create a button for restart the game
        ImageView restart = new ImageView(restart_normal);
        restart.setX(WIDTH/2-100);
        restart.setY(HEIGHT/2 + 100);
        restart.setOnMouseEntered(event -> restart.setImage(restart_hover));
        restart.setOnMouseExited(event -> restart.setImage(restart_normal));
        restart.setOnMouseClicked(event -> main.new_game());

        timeline.setOnFinished(event->{
            nextLetter = 0;
            Timeline tl = new Timeline(new KeyFrame(Duration.seconds(2.0/score_txt.length()), event1 -> score_text.setText(score_text.getText()+score_txt.charAt(nextLetter++))));
            tl.setCycleCount(score_txt.length());
            tl.play();
            tl.setOnFinished(event1 -> {
                // add the button for restart the game after all the text have been displayed
                list.add(restart);
            });
        });

        // Add the Game Over screen to the scene
        list.add(text);
        list.add(score_text);
    }

    /**
     * read the highest score from the file
     *
     * @return the highest score
     */
    public Pair<Integer, Integer> read(){
        try{
            FileInputStream is = new FileInputStream("record.dat");
            BufferedInputStream bis = new BufferedInputStream(is);
            DataInputStream in = new DataInputStream(bis);
            int minutes = in.readInt();
            in.readChar();
            int seconds = in.readInt();
            in.close();
            return new Pair<>(minutes, seconds);
        } catch (IOException e){
            return new Pair<>(0, 0);
        }
    }

    /**
     * record the current score to the file
     */
    public void record(){
        try {
            FileOutputStream os = new FileOutputStream("record.dat");
            BufferedOutputStream bos = new BufferedOutputStream(os);
            DataOutputStream out = new DataOutputStream(bos);
            out.writeInt(minutes);
            out.writeChar('\n');
            out.writeInt(seconds);
            //System.out.println("Recorded");
            out.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
