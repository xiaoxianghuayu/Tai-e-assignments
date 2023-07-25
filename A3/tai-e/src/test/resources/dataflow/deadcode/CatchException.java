class CatchException {

    void catch_test() {
        try {
            int a = 25/0;
        } catch (java.lang.Exception e) {
            String msg = e.getMessage();
        }
    }

}