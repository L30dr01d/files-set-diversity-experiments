int points(const char* const games[10]) {
    int total = 0;

    for (int i = 0; i < 10; ++i) {
        int home_goals = games[i][0] - '0';
        int away_goals = games[i][2] - '0';

        if (home_goals > away_goals) {
            total += 3;
        } else if (home_goals == away_goals) {
            total += 1;
        }
    }

    return total;
}