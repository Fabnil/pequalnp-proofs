#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

using Cells = std::array<uint64_t, 6>;
struct Rectangle {
    int area;
    Cells cells;
};
struct Option {
    int index;
    int gain;
};

std::vector<Rectangle> boxes;
std::vector<int> trace;
std::chrono::steady_clock::time_point deadline;
uint64_t nodes = 0;
bool interrupted = false;

int gain(const Cells &covered, const Cells &rectangle) {
    int total = 0;
    for (int j = 0; j < 6; ++j)
        total += __builtin_popcountll(rectangle[j] & ~covered[j]);
    return total;
}

bool search(const Cells &covered, int missing, int slots, const std::vector<Option> &ancestors) {
    if (missing == 0)
        return true;
    if (slots == 0)
        return false;
    if ((++nodes & 511) == 0 && std::chrono::steady_clock::now() >= deadline) {
        interrupted = true;
        return false;
    }
    const int min_gain = missing - 54 * (slots - 1);
    std::vector<Option> options;
    std::array<int, 55> gains{};
    std::array<int, 360> frequency{};
    Cells attainable{};
    for (const Option parent : ancestors) {
        if (parent.gain < min_gain)
            continue;
        const Cells &b = boxes[parent.index].cells;
        int add = gain(covered, b);
        if (add < min_gain)
            continue;
        options.push_back({parent.index, add});
        ++gains[add];
        for (int j = 0; j < 6; ++j) {
            uint64_t bits = b[j] & ~covered[j];
            attainable[j] |= bits;
            while (bits != 0) {
                const int cell = 64 * j + __builtin_ctzll(bits);
                ++frequency[cell];
                bits &= bits - 1;
            }
        }
    }
    if (options.empty() || gain(covered, attainable) != missing)
        return false;
    int optimistic = 0, left = slots;
    for (int a = 54; a >= min_gain && left > 0; --a) {
        const int count = std::min(left, gains[a]);
        optimistic += count * a;
        left -= count;
    }
    if (optimistic < missing)
        return false;
    int pivot = -1;
    for (int c = 0; c < 360; ++c) {
        if (frequency[c] && (pivot < 0 || frequency[c] < frequency[pivot]))
            pivot = c;
    }
    if (pivot < 0)
        return false;
    const int word = pivot / 64;
    const uint64_t bit = uint64_t{1} << (pivot % 64);
    std::sort(options.begin(), options.end(), [](Option a, Option b) { return a.gain > b.gain; });
    for (const Option b : options) {
        const Cells &mask = boxes[b.index].cells;
        if ((mask[word] & bit) == 0)
            continue;
        Cells next = covered;
        for (int j = 0; j < 6; ++j)
            next[j] |= mask[j];
        trace.push_back(b.index);
        if (search(next, missing - b.gain, slots - 1, options))
            return true;
        trace.pop_back();
        if (interrupted)
            return false;
    }
    return false;
}

int main() {
    int size, nanchors;
    std::cin >> size >> nanchors;
    std::vector<int> anchors(nanchors);
    for (int &i : anchors)
        std::cin >> i;
    std::vector<Option> all;
    for (int i = 0; i < size; ++i) {
        Rectangle box;
        std::cin >> box.area;
        for (uint64_t &word : box.cells)
            std::cin >> word;
        boxes.push_back(box);
        all.push_back({i, box.area});
    }
    deadline = std::chrono::steady_clock::now() + std::chrono::seconds(75);
    for (int a : anchors) {
        trace = {a};
        nodes = 0;
        const bool found = search(boxes[a].cells, 360 - boxes[a].area, 6, all);
        std::cout << "anchor " << a << (found ? " hit " : interrupted ? " timeout " : " excluded ")
                  << nodes << " nodes" << std::endl;
        if (found) {
            for (int i : trace)
                std::cout << i << ' ';
            std::cout << std::endl;
        }
        if (found)
            return 1;
        if (interrupted)
            return 2;
    }
}
