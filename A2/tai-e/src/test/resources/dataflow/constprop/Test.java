class Test {
    private int anInt;

    void method_call() {
        return_one();
        int a = return_one();
    }

    int return_one() {
        return 1;
    }

    void obj_load() {
        Test o = new Test();
        int a = o.anInt;
//        o.anInt = 999;
    }
}