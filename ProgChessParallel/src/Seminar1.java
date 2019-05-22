import Rules.*;

import java.io.*;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.locks.ReentrantLock;

class Piece{
    int x = 0,y = 0, color;  //board[y][x] = (x,y) CUZ BOARD IS TILTED
    int[][] directions = new int[][]{};
    boolean scalable = false;

    //iterating procedures
    int it, scale;

    boolean isMoveValid(int[][] board, int xp, int yp){ //what name says
        return (yp < 8 && yp >= 0 && xp >= 0 && xp < 8 && color*board[yp][xp]<=0);
    }

    private void nextValidMove(int[][] board){ //also what function name says
        if(scalable){
            scale++;
            if(!isMoveValid(board,x+scale*directions[it][1],y+scale*directions[it][0])) {
                //if out of board or field is a friendly piece
                scale = 1;
                it++;
            }
        }
        else it++;

        while(it<directions.length && !isMoveValid(board,x+directions[it][1],y+directions[it][0])) {
            //if out of board or field is a friendly piece
            it++;
        }
    }

    void initIter(int[][] board){ //initiate iterator
        it=0;
        scale=1;
        if(!isMoveValid(board,x+directions[it][1],y+directions[it][0])){
            nextValidMove(board);
        }
    }

    /*  iterate through valid moves
        returns (y,x) cuz board is oriented WRONG*/
    int[] nextMove(int[][] board){
        if(it<directions.length){
            int[] r=new int[]{y,x};

            r[0]+=scale*directions[it][0];
            r[1]+=scale*directions[it][1];

            nextValidMove(board);

            return r;
        }
        return null;
    }
}

class King extends Piece{
    King(int x_in, int y_in, int color_in){
        x=x_in;
        y=y_in;
        directions = new int[][]{{1, 1}, {-1, 1}, {-1, -1}, {1, -1}, {1, 0}, {0, 1}, {-1, 0}, {0, -1}};
        scalable = false;
        color=color_in;
    }
}

class Pawn extends Piece{
    Pawn(int color_in){
        directions = new int[][]{{color_in*1, -1}, {color_in*1, 1}};
    }

    Pawn(int x_in, int y_in, int color_in){
        x=x_in;
        y=y_in;
        directions = new int[][]{{color_in*1, 0}, {color_in*1, -1}, {color_in*1, 1}};
        scalable = false;
        color=color_in;
    }

    boolean isMoveValid(int[][] board, int xp, int yp){ //what name says
        if(!(yp < 8 && yp >= 0 && xp >= 0 && xp < 8)) return false;
        if(board[yp][xp]==color*-6) return false;
        if(xp-x==0) return color*board[yp][xp]==0;
        else return color*board[yp][xp]<0;
    }

    ArrayList<int[]> validMoves(int[][] board){
        ArrayList<int[]> r = new ArrayList<>();
        for(int i=0;i<3;++i){
            if(isMoveValid(board,x+directions[i][1],y+directions[i][0])) r.add(directions[i]);
        }
        return r;
    }

    int pawnValue(int[][] board, int ml, int ekx, int eky){
        int val=-2;

        if(y==0||y==7) return 2;
        if(x+1<8 && board[y+directions[1][0]][x+1] == color*-6) return 1;
        if(x-1>=0 && board[y+directions[1][0]][x-1] == color*-6) return 1;
        if(ml==0) return val;

        if(Math.abs(ekx-x)<3 && (eky-y)*color<3 && (eky-y)*color>-1){
            val=1;
        }

        ArrayList<int[]> moves = validMoves(board);
        int rec;
        for(int i=0;i< moves.size();++i){
            rec =(new Pawn(x+moves.get(i)[1],y+moves.get(i)[0],color)).pawnValue(board,ml-1,ekx,eky);
            if(rec==3 || rec == 1 && val == 2 || rec == 2 && val == 1) return 3;
            else if (rec>0) val=rec;
        }

        return val;
    }
}




public class Seminar1 {


    static long timesum;

    private final static int h_CHECKMATE = 1000000;
    private final static int const_base = 1000;
    private final static int const_cvrd = 25;
    private final static int const_a = 7;
    private final static boolean use_dfs = false;
    private final static int const_onemove = -50;
    private final static int const_omdist = -120;
    private final static int const_bd = 20; //bishop
    private final static int const_kd = 7; //knight
    private final static int const_rd = 10; //rook
    private final static int const_path = 20;
    private final static int const_promo = 60;
    private final static int const_cap = 30;
    private final static int const_pmp = -50;
    private final static boolean use_inhe = false;
    private static int foundFasterMate;

    private static int mhDistance(int x1, int y1, int x2, int y2) {
        return Math.abs(x1 - x2) + Math.abs(y1 - y2);
    }

    private static class Movew{
        public String alg;
        public String nalg;
        public Move move;

        Movew(Move move_in){
            move=move_in;
            move.setAlgebraicNotaion(true);
            alg = move.toString();
            move.setAlgebraicNotaion(false);
            nalg = move.toString();
        }
    }

    private static class Sequence implements Comparator<Sequence> {
        Chessboard board;
        public ArrayList<Movew> seq;
        public int h;
        private boolean initial;

        //stats
        public static int color;
        public King eKing;
        private static int fnc; //first not covered

        private boolean calculated;
        private int[][] boardA;  
        private int nnc; //now not covered


        //last move data
        public int from_x, from_y, to_x, to_y, piece, promo, cap;

        private int pieceToInt(char c) {
            switch (c) {
                case 'O':
                    return 6;
                case 'K':
                    return 6;
                case 'Q':
                    return 5;
                case 'R':
                    return 4;
                case 'N':
                    return 3;
                case 'B':
                    return 2;
                default:
                    return 1;
            }
        }

        private int fieldToInt(char c){
            switch(c) {
                case 'a':
                    return 0;
                case 'b':
                    return 1;
                case 'c':
                    return 2;
                case 'd':
                    return 3;
                case 'e':
                    return 4;
                case 'f':
                    return 5;
                case 'g':
                    return 6;
                default:
                    return 7;
            }
        }

        private void getLastMoveData(Movew move){
            piece = pieceToInt(move.alg.charAt(0));
            from_x = fieldToInt(move.nalg.charAt(0));
            from_y = ((int) move.nalg.charAt(1)) - 49;
            to_x = fieldToInt(move.nalg.charAt(3));
            to_y = ((int) move.nalg.charAt(4)) - 49;
            promo=-1;
            cap = move.alg.contains("x")?1:0;
            //System.out.println(move.nalg.charAt(move.nalg.length()-1));
            if(!Character.isDigit(move.nalg.charAt(move.nalg.length()-1))) promo = pieceToInt(move.nalg.charAt(move.nalg.length()-1));
        }
        //last move data

        //init
        Sequence(){}

        Sequence(Chessboard board_in){ //initial empty sequence
            seq = new ArrayList<Movew>();
            initial=true;
            h=const_base;
            board = board_in.copy();

            //stats init
            calculated=false;
            color = board.getColor();
            boardA = board.getBoard();
            loop1: for(int i=0;i<boardA.length;++i){
                for(int j=0;j<boardA[i].length;++j){
                    if(boardA[i][j] == color*board.KING_B){
                        eKing=new King(j,i,-color);
                        break loop1;
                    }
                }
            }
            fnc = getNnc();
        }

        Sequence(Sequence sequence, Movew move, Chessboard board_in, int h_in){ //extended sequence
            initial=false;
            eKing = new King(sequence.eKing.x,sequence.eKing.y,-color);
            seq = new ArrayList<Movew>(sequence.seq);
            seq.add(move);
            h=h_in;
            board=board_in;
            calculated=false;
            getLastMoveData(move);
        }
        //init

        //calculate heuristics
        //harder to calculate values
        public void calculate(){
            calculated=true;
            boardA=board.getBoard();

            //not covered count
            eKing.initIter(boardA);
            nnc=0;
            int[] move = eKing.nextMove(boardA);
            while(move != null){
                if(!Rules.isCovered(boardA,move[0],move[1],color)) nnc++;
                move = eKing.nextMove(boardA);
            }
        }

        public int getNnc(){
            if(!calculated){
                calculate();
            }

            return nnc;
        }


        public int evalh() {

            int boardStatus = board.getGameStatus();
            if (boardStatus == board.CHECKMATE) { //checkmategetNnc()
                if (board.getMovesLeft() > 0) {   //wrong time for mate
                    h = -1;
                    foundFasterMate = 1;
                    //TODO: re-evaluate all after this?
                } else h = h_CHECKMATE; //right time, found solution
            }
            else if (board.getMovesLeft() == 0) h = -1;  //out of moves, discard
            else if (boardStatus == board.CHECK){
                h = -1;
            } //check, calc check fields then discard
            else if (boardStatus == board.DRAW) h = -1;//invalid move discard
            else {
                int change = const_base + 100 / (board.getMovesLeft() + const_a); //higher priority for moves further in + base

                if(use_dfs){
                    h = change;
                    return h;
                }

                //if(board.getMovesLeft()==1) change+=0;
                change += (fnc - getNnc()) * const_cvrd; //covered fields

                int cd = mhDistance(eKing.x,eKing.y,to_x,to_y);
                if(cd<4&&cd>1) change += const_cap*cap;

                //punish generally more useless moves
                if(foundFasterMate == 0) {
                    //king or pawn single move punishment
                    if (piece == 1){

                        int peval = (new Pawn(to_x,to_y,color)).pawnValue(board.getBoard(),board.getMovesLeft(),eKing.x,eKing.y);
                        if(peval == 1) peval = 2;
                        change += (peval<0?const_pmp:(peval==3?0:-10));

                        if(from_y == (color == 1 ? 1 : 6) && Math.abs(from_y - to_y) == 1) change += const_onemove;
                        if(from_y == (color == 1 ? 6 : 1)) change += const_promo;
                        int dist = 10;
                        if(Math.abs(eKing.x-to_x)<3) dist = Math.abs(eKing.y-to_y) - (eKing.x-to_x == 0?2:1); //TODO: check this recursively with pawn moves on board
                        dist = Math.min(dist, Math.abs(to_x - (color==1?7:0)));
                        if(dist>=board.getMovesLeft()){
                            change +=const_omdist/(board.getMovesLeft() + 1);
                            if(from_y == (color == 1 ? 1 : 6) && Math.abs(from_y - to_y) == 1) change += const_onemove;
                        }
                    }

                    if (piece == 6) {
                        change += const_onemove; //constant for bad king move

                        int pdist = Math.max(Math.abs(eKing.x-from_x),Math.abs(eKing.y-from_y));
                        int dist = Math.max(Math.abs(eKing.x-to_x),Math.abs(eKing.y-to_y));
                        if(dist>board.getMovesLeft()+1) change +=const_omdist/(board.getMovesLeft()+2);
                    }
                    //king or pawn single move punishment
                }

                //reward generally good moves
                if(piece == board.BISHOP || piece == board.QUEEN && (to_x != from_x || to_y!=from_y) || piece == board.KING){
                    int dist = Math.max(Math.abs(eKing.x-to_x),Math.abs(eKing.y-to_y));
                    int pdist = Math.max(Math.abs(eKing.x-from_x),Math.abs(eKing.y-from_y));
                    if(pdist>2){
                        dist=Math.max(dist,2);
                        change+=(pdist-dist)*const_bd;
                        if(piece == board.KING && pdist>dist && dist < board.getMovesLeft() + 2){
                            change+=const_onemove/3+5;
                        }
                    }
                }
                if(piece == board.KNIGHT){
                    int dist = mhDistance(eKing.x, eKing.y, to_x, to_y);
                    int pdist = mhDistance(eKing.x, eKing.y, from_x, from_y);
                    dist=Math.max(dist,2);
                    if(pdist>2){
                        change+=(pdist-dist)*const_kd;
                    }
                    if(dist>3&&(to_x==0||to_y==0||to_x==7||to_y==7)){
                        change+=const_onemove;
                    }
                }
                if(piece == board.ROOK || piece == board.QUEEN && (to_x == from_x || to_y==from_y) || piece == board.KING){
                    int rookBonus = 0;
                    int dist = mhDistance(eKing.x, eKing.y, to_x, to_y);
                    int pdist = mhDistance(eKing.x, eKing.y, from_x, from_y);
                    if(pdist>2){
                        rookBonus+=(pdist-dist)*const_rd;
                        if(piece == board.KING && pdist>dist && dist < board.getMovesLeft() + 2){
                            rookBonus+=(pdist-dist)*const_onemove/3+5;
                        }
                    }
                    if(Math.abs(dist-pdist)==1) rookBonus-=const_rd;

                    if(piece!= board.KING){} //TODO: second direction check

                    change+=rookBonus;
                }


                //free up bonus
                boardA = board.getBoard();
                if(isBlocking(from_x,from_y,2)) change += const_path * ((board.getMovesLeft()-1)/2);
                if(isBlocking(from_x,from_y,1)) change += const_path * ((board.getMovesLeft()+1)/3);




                //TODO: evaluate move based on fields near king, king move (done), pieces protect (done), pin
                h=use_inhe?(10*change-h)/9:change;
            }
            return h;
        }

        private boolean isBlocking(int px, int py, int pc){
            int cpx = px;
            int cpy = py;
            int pcs=0;
            while(cpx+1<8 && pcs<pc  ){//&& eKing.x <= px){
                cpx++;
                if(boardA[cpy][cpx]==color*board.ROOK || boardA[cpy][cpx]==color*board.QUEEN) return true;
                else if(boardA[cpy][cpx]*color > 0) pcs++;
                else if(boardA[cpy][cpx] == 0) continue;
            }

            cpx = px;
            cpy = py;
            pcs=0;
            while(cpx-1>0 && pcs<pc ){//&& eKing.x >= px){
                cpx--;
                if(boardA[cpy][cpx]==color*board.ROOK || boardA[cpy][cpx]==color*board.QUEEN) return true;
                else if(boardA[cpy][cpx]*color > 0) pcs++;
                else if(boardA[cpy][cpx] == 0) continue;
            }

            cpx = px;
            cpy = py;
            pcs=0;
            while(cpy+1<8 && pcs<pc ){//&&eKing.y <= py){
                cpy++;
                if(boardA[cpy][cpx]==color*board.ROOK || boardA[cpy][cpx]==color*board.QUEEN) return true;
                else if(boardA[cpy][cpx]*color > 0) pcs++;
                else if(boardA[cpy][cpx] == 0) continue;
            }

            cpx = px;
            cpy = py;
            pcs=0;
            while(cpy-1>0 && pcs<pc ){//&& eKing.y >= py){
                cpy--;
                if(boardA[cpy][cpx]==color*board.ROOK || boardA[cpy][cpx]==color*board.QUEEN) return true;
                else if(boardA[cpy][cpx]*color > 0) pcs++;
                else if(boardA[cpy][cpx] == 0) continue;
            }


            /*Bishop b=new Bishop();
            for(int i=0;i<b.directions.length;++i){
                int dirx = b.directions[i][1];
                int diry = b.directions[i][0];
                cpx = px;
                cpy = py;
                pcs=0;
                while(cpx + dirx >= 0 && cpx + dirx < 8 && cpy + diry >= 0 && cpy + diry < 8 && pcs<pc
                        && Math.signum(eKing.x-px) != dirx && Math.signum(eKing.y-py) != diry){
                    cpx+=dirx;
                    cpy+=diry;
                    if(boardA[cpy][cpx]==color*board.BISHOP || boardA[cpy][cpx]==color*board.QUEEN){
                        return true;
                    }
                    else if(boardA[cpy][cpx]*color > 0) pcs++;
                    else if(boardA[cpy][cpx] == 0) continue;
                }
            }*/
            return false;
    /*
            Knight k=new Knight();
            for(int i=0;i<k.directions.length;++i){
                int dirx = k.directions[i][1];
                int diry = k.directions[i][0];
                cpx = eKing.x + dirx;
                cpy = eKing.y + diry;
                if(cpx >= 0 && cpx < 8 && cpy >= 0 && cpy < 8 && boardA[cpy][cpx]==color*board.KNIGHT){
                    checkFF[cpy][cpx]++;
                }
            }

            Pawn p = new Pawn(-color);
            for(int i=0;i<p.directions.length;++i){
                int dirx = p.directions[i][1];
                int diry = p.directions[i][0];
                cpx = eKing.x + dirx;
                cpy = eKing.y + diry;
                if(cpx >= 0 && cpx < 8 && cpy >= 0 && cpy < 8 && boardA[cpy][cpx]==color*board.PAWN){
                    checkFF[cpy][cpx]++;
                }
            }
            */
        }

        public int len(){
            return seq.size();
        }

        public int compare(Sequence s1, Sequence s2){
            return s2.h - s1.h;
        }

        public ArrayList<String> to_strings(int type){
            ArrayList<String> r = new ArrayList<>();
            for (Movew move : seq) {
                if(type == 0){
                    r.add(move.nalg);
                }
                else if(type > 0){
                    r.add(move.alg);
                }
                if (type == 2){
                    r.set(r.size()-1, r.get(r.size()-1).charAt(0) + move.nalg);
                }
            }
            return r;
        }

        public String to_string(){
            return String.join(";",to_strings(0));
        }

        public String toKey(boolean domove){
                int save=0;
                if(domove) {
                    boardA = board.getBoard();
                    save = boardA[to_y][to_x];
                    boardA[to_y][to_x] = boardA[from_y][from_x];
                    if (promo > 0) {
                        boardA[to_y][to_x] = color * promo;
                    }
                    boardA[from_y][from_x] = 0; //artificially make move
                }

                String[] str = board.getFEN().split(" ");

                if(domove) {
                    boardA[from_y][from_x] = boardA[to_y][to_x];
                    if (promo > 0) boardA[from_y][from_x] = color * 1;
                    boardA[to_y][to_x] = save; //reverse artificial move
                }
                return str[0];
        }
    }

    private static String sol;
    private static PriorityQueue<Sequence> queue;
    private static ConcurrentHashMap<String, Sequence> HM;

    static ReentrantLock lock = new ReentrantLock();
    static ReentrantLock lock2 = new ReentrantLock();

    private static Runnable runf = () ->{
        ArrayList<Move> tmpMoves;
        ArrayList<Movew> possibleMoves;
        Sequence ns;  //new sequence (temporary)
        int h;//temp eval variable
        Chessboard board;
        Sequence cs;

        while(sol.equals("")){
            cs=null;
            lock.lock();
            if(queue.size()!=0) {
                cs = queue.poll(); //current sequence
            }
            lock.unlock();
            if(cs!=null) {
                if (HM.get(cs.toKey(false)) != cs) {
                    continue;
                }
                board = cs.board;
                tmpMoves = board.getMoves();
                possibleMoves = new ArrayList<>();

                lock2.lock();
                    for (Move move : tmpMoves) {
                        possibleMoves.add(new Movew(move));
                    }
                lock2.unlock();

                for (Movew move : possibleMoves) {
                    if (board.getMovesLeft() == 1) {
                        if (move.alg.charAt(move.alg.length() - 1) == '#') {
                            sol = (new Sequence(cs, move, board, cs.h)).to_string();
                            return;
                        }
                    } else {
                        if(move.alg.charAt(move.alg.length()-1)=='+' || move.alg.charAt(0)=='O'
                            || move.nalg.charAt(move.nalg.length()-1)=='B' || move.nalg.charAt(move.nalg.length()-1)=='R'
                        ){
                            continue;
                        }

                        Chessboard newBoard = board.copy();
                        ns = new Sequence(cs, move, newBoard, cs.h);

                        String nsKey = ns.toKey(true);
                        Sequence es = HM.get(nsKey);
                        if (es != null && es.len() <= ns.len()) {
                            continue;
                        }

                        newBoard.makeMove(move.move);

                        h = ns.evalh();


                        if (h >= 0) { //h<0 wrong moves (check)
                            HM.put(nsKey, ns);
                            lock.lock();
                            queue.add(ns);
                            lock.unlock();
                        }
                    }
                }
            }
        }
    };

    private static String Astar(Chessboard board){
        foundFasterMate = 0;
        sol="";
        //initialize
        queue = new PriorityQueue<>(300, new Sequence());
        Sequence frst = new Sequence(board);
        queue.add(frst);
        HM = new ConcurrentHashMap<String, Sequence>(1000,0.40f);
        HM.put(frst.toKey(false),frst);
        Thread t1 = new Thread(runf);
        Thread t2 = new Thread(runf);
       Thread t3 = new Thread(runf);
        Thread t4 = new Thread(runf);
        t1.start();
       t2.start();
        t3.start();
        t4.start();
        try{
            t1.join();
            t2.join();
            t3.join();
            t4.join();
        }catch(Exception e){System.out.println(e);}

        return sol;
    }


    public static void main (String args[]) throws IOException {
        //Scanner sc = new Scanner(System.in);
        String fenIn;
        String fileName; //= sc.nextLine();

        timesum = 0;
        for (int i = 1; i <= 60; ++i) {
            long stime = System.nanoTime();

            //read
            System.out.print(i + " ");
            fileName = "in/" + i + ".txt";
            //fileName = args[0];
            File file = new File(fileName);
            FileReader fr = new FileReader(file);
            BufferedReader br = new BufferedReader(fr);
            fenIn = br.readLine();

            //solve
            Chessboard board = Chessboard.getChessboardFromFEN(fenIn);

            String result = Astar(board);

            //print
            long etime = System.nanoTime();
            System.out.print(" " + (etime - stime) / 1000000 + " ");
            if (result != null) {
                System.out.println(result);
            }
            timesum += etime - stime;
        }
        System.out.println(timesum / 1000000);
        //
    }/**/

/*
    public static void main (String args[]) throws IOException {
        //Scanner sc = new Scanner(System.in);
        String fenIn;
        String fileName; //= sc.nextLine();

        fileName = args[0];
        File file = new File(fileName);
        FileReader fr = new FileReader(file);
        BufferedReader br = new BufferedReader(fr);
        fenIn = br.readLine();

        //solve
        Chessboard board = Chessboard.getChessboardFromFEN(fenIn);

        String result = Astar(board);

        if (result != null) {
            System.out.println(result);
        }
    }/**/
}
