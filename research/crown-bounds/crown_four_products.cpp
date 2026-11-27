// Pair four-biclique covers of four crowns, then share OR subexpressions.
#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <stdexcept>
#include <utility>
#include <vector>

struct Rectangle {
    unsigned rows;
    unsigned columns;
    unsigned edges;
};

using Cover = std::array<Rectangle, 4>;
using Mask = std::uint64_t;

struct State {
    std::array<int, 4> covers;
    std::array<int, 16> partner;
};

struct Gate {
    bool is_or;
    int left;
    int right;
};

std::vector<Cover> covers_of_crown() {
    std::vector<Rectangle> rectangles;
    unsigned target = 0;
    for (unsigned rows = 1; rows < 16; ++rows) {
        for (unsigned columns = 1; columns < 16; ++columns) {
            if (rows & columns) continue;
            unsigned edges = 0;
            for (unsigned row = 0; row < 4; ++row) {
                if ((rows >> row) & 1) edges |= columns << (4 * row);
            }
            target |= edges;
            rectangles.push_back({rows, columns, edges});
        }
    }
    const int size = static_cast<int>(rectangles.size());
    std::vector<Cover> result;
    for (int a = 0; a < size; ++a) {
        for (int b = a + 1; b < size; ++b) {
            for (int c = b + 1; c < size; ++c) {
                for (int d = c + 1; d < size; ++d) {
                    Cover cover = {rectangles[a], rectangles[b], rectangles[c], rectangles[d]};
                    if ((cover[0].edges | cover[1].edges | cover[2].edges | cover[3].edges) == target) {
                        result.push_back(cover);
                    }
                }
            }
        }
    }
    return result;
}

State initial(const std::vector<Cover>& covers) {
    State state{};
    std::array<int, 16> labels{};
    for (int b = 0; b < 4; ++b) {
        const bool row_stars = (b % 2 == 0);
        auto match = std::find_if(covers.begin(), covers.end(), [&](const Cover& cover) {
            return std::all_of(cover.begin(), cover.end(), [&](const Rectangle& r) {
                return std::popcount(row_stars ? r.rows : r.columns) == 1;
            });
        });
        state.covers[b] = static_cast<int>(match - covers.begin());
        for (int i = 0; i < 4; ++i) {
            labels[4 * b + std::countr_zero(row_stars ? (*match)[i].rows : (*match)[i].columns)] = 4 * b + i;
        }
    }
    for (int i = 0; i < 16; ++i) {
        state.partner[labels[i]] = labels[i ^ 4];
    }
    return state;
}

int evaluate(const State& state, const std::vector<Cover>& covers, std::vector<Gate>* gates = nullptr) {
    std::array<Mask, 16> factors{};
    std::array<std::pair<int, int>, 8> products{};
    int factor_count = 0;
    int product_count = 0;
    auto slot = [&](Mask value) {
        for (int i = 0; i < factor_count; ++i) {
            if (factors[i] == value) return i;
        }
        factors[factor_count] = value;
        return factor_count++;
    };
    for (int i = 0; i < 16; ++i) {
        int j = state.partner[i];
        if (i > j) continue;
        const int a = i / 4, b = j / 4;
        const Rectangle& x = covers[state.covers[a]][i % 4];
        const Rectangle& y = covers[state.covers[b]][j % 4];
        if (a == b && ((x.rows & y.rows) || (x.columns & y.columns))) return 100;
        const Mask left = (Mask(x.rows) << (4 * a)) | (Mask(y.columns) << (16 + 4 * b));
        const Mask right = (Mask(y.rows) << (4 * b)) | (Mask(x.columns) << (16 + 4 * a));
        products[product_count++] = {slot(left), slot(right)};
    }

    int next = 32;
    while (true) {
        std::array<unsigned char, 64 * 64> counts{};
        int best_count = 1;
        int best_key = 64 * 64;
        for (int i = 0; i < factor_count; ++i) {
            for (Mask first = factors[i]; first; first &= first - 1) {
                int a = std::countr_zero(first);
                for (Mask second = first & (first - 1); second; second &= second - 1) {
                    int key = a * 64 + std::countr_zero(second);
                    int count = ++counts[key];
                    if (count > best_count || (count == best_count && count > 1 && key < best_key)) {
                        best_count = count;
                        best_key = key;
                    }
                }
            }
        }
        if (best_count == 1) break;
        int a = best_key / 64, b = best_key % 64;
        Mask mask = (Mask(1) << a) | (Mask(1) << b);
        for (int i = 0; i < factor_count; ++i) {
            if ((factors[i] & mask) == mask) factors[i] = (factors[i] ^ mask) | (Mask(1) << next);
        }
        if (gates) gates->push_back({true, a, b});
        ++next;
    }

    int cost = next - 32 + 2 * product_count - 1;
    if (!gates) {
        for (int i = 0; i < factor_count; ++i) cost += std::popcount(factors[i]) - 1;
        return cost;
    }

    std::array<int, 16> wires{};
    for (int i = 0; i < factor_count; ++i) {
        Mask inputs = factors[i];
        int output = std::countr_zero(inputs);
        for (inputs &= inputs - 1; inputs; inputs &= inputs - 1) {
            gates->push_back({true, output, std::countr_zero(inputs)});
            output = next++;
        }
        wires[i] = output;
    }
    const int first_product = next;
    for (const auto& [a, b] : products) {
        gates->push_back({false, wires[a], wires[b]});
        ++next;
    }
    int output = first_product;
    for (int i = 1; i < product_count; ++i) {
        gates->push_back({true, output, first_product + i});
        output = next++;
    }
    return next - 32;
}

void validate(const std::vector<Gate>& gates) {
    for (int row = 0; row < 16; ++row) {
        for (int column = 0; column < 16; ++column) {
            std::array<bool, 128> wires{};
            wires[row] = wires[16 + column] = true;
            int index = 32;
            for (const auto& g : gates) {
                wires[index++] = g.is_or ? wires[g.left] || wires[g.right] : wires[g.left] && wires[g.right];
            }
            if (wires[index - 1] != (row / 4 == column / 4 && row % 4 != column % 4)) {
                throw std::runtime_error("invalid circuit");
            }
        }
    }
}

int main(int argc, char** argv) {
    const int iterations = argc > 1 ? std::stoi(argv[1]) : 120000;
    const unsigned seed = argc > 2 ? static_cast<unsigned>(std::stoul(argv[2])) : 20261127;
    const auto covers = covers_of_crown();
    auto baseline = initial(covers);
    auto best = baseline;
    int best_cost = evaluate(best, covers);
    std::cout << "covers " << covers.size() << ", baseline " << best_cost << std::endl;
    std::mt19937 rng(seed);
    std::uniform_real_distribution<double> uniform(0.0, 1.0);
    auto current = baseline;
    int current_cost = best_cost;
    int step = 0;
    constexpr int restart = 15000;
    for (; step < iterations && best_cost > 42; ++step) {
        if (step % restart == 0) {
            current = (step / restart % 2 == 0) ? best : baseline;
            current_cost = evaluate(current, covers);
        }
        State candidate = current;
        if (rng() % 5 < 2) {
            candidate.covers[rng() % 4] = static_cast<int>(rng() % covers.size());
        } else {
            int a = rng() % 16, b = rng() % 16;
            int c = candidate.partner[a], d = candidate.partner[b];
            if (a == b || a == d) continue;
            candidate.partner[a] = d;
            candidate.partner[d] = a;
            candidate.partner[b] = c;
            candidate.partner[c] = b;
        }
        const int cost = evaluate(candidate, covers);
        if (cost < best_cost) {
            best_cost = cost;
            best = candidate;
        }
        const double progress = (step % restart) / static_cast<double>(restart);
        const double temperature = 1.3 * (1 - progress) + 0.12;
        if (cost <= current_cost || uniform(rng) < std::exp((current_cost - cost) / temperature)) {
            current = candidate;
            current_cost = cost;
        }
    }
    std::vector<Gate> gates;
    if (evaluate(best, covers, &gates) != best_cost) throw std::runtime_error("inconsistent gate count");
    validate(gates);
    std::cout << "best " << best_cost << " after " << step << " proposals" << std::endl;
    if (best_cost <= 42) {
        for (const auto& g : gates) std::cout << (g.is_or ? "OR " : "AND ") << g.left << ' ' << g.right << '\n';
    }
}
