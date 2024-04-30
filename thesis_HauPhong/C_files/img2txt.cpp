#include <opencv2/opencv.hpp>
#include <fstream>
#include <iomanip>
#include "iostream"
#include "svdpi.h"
#include "stdio.h"

using namespace cv;
using namespace std;

extern "C" void dumamay() {
    string imagePath = "/home/hao/Documents/cpp_test/images/1.png"; // Provide the path to the MNIST image
    string textPath = "/home/hao/Documents/cpp_test/output_files/1_C.txt"; // Provide the path for the text file

    // Read MNIST image
    Mat image = imread(imagePath, IMREAD_GRAYSCALE);
    
    if (image.empty()) {
        cerr << "Error: Could not read image." << endl;
    }

    // Save image pixel values to text file
    ofstream outputFile(textPath);

    if (!outputFile.is_open()) {
        cerr << "Error: Could not open text file." << endl;
    }

    for (int i = 0; i < image.rows; ++i) {
        for (int j = 0; j < image.cols; ++j) {
            int pixelValue = static_cast<int>(image.at<uchar>(i, j));
            if (pixelValue == 0) {
                outputFile << "00" << endl;
            } else {
                outputFile << setw(2) << setfill('0') << hex << uppercase << pixelValue << endl;
            }
        }
    }

    outputFile.close();
    
    cout << "MNIST image converted to text file successfully.\n";
}

