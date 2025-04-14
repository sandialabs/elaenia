float determinant(float a, float b, float c, 
                  float d, float e, float f,
                  float g, float h, float i) {
    return ((((a * e) * i) + ((b * f) * g) + ((c * d) * h) -
            (((c * e) * g) + ((b * d) * i)) + ((a * f) * h)));
}

int main() {
    determinant(0.1, 0.2, 0.3,
                0.4, 0.5, 0.6,
                0.7, 0.8, 0.9);
    return 1;
}
