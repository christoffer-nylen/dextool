bool sample(bool a, bool b, bool c, bool ready, bool enabled) {
    if (a && b || !c) {
        return ready || enabled;
    }

    return !ready;
}
