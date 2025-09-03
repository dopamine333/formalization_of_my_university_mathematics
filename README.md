# 我的大學數學公式化 (Formalization of My University Mathematics)

這是一個個人專案，旨在使用 [Lean 4](https://leanprover.github.io/) 這個互動式定理證明輔助工具，將大學時期所學的數學知識進行公式化、系統化的整理與證明。

## 專案目標

本專案的目標是為各種數學領域建立一個嚴謹、無歧義、且可被電腦驗證的數位知識庫。透過這個過程，不僅能加深對數學概念的理解，也能探索使用形式化方法來表達複雜數學思想的可能性。

## 專案結構

主要的 Lean 原始碼位於 `FormalizationOfMyUniversityMathematics/` 資料夾中，並依照不同的數學學科進行分類：

- `Abstract_Algebra_II/`: 抽象代數 (群論、環論等)
- `Combinatorics/`: 組合學
- `Commutator/`: 交換子理論
- `GroupAsReductionSystem/`: 將群視為歸約系統
- `InductiveType/`: 歸納類型
- `Introduction_to_Analysis/`: 分析學導論
- `ModelTheory/`: 模型論
- `My_Filter/`: 濾波器理論
- `Numerical_Analysis/`: 數值分析
- `PartialDifferentialEquationAnIntroduction/`: 偏微分方程導論
- `Statistics/`: 統計學
- `Vector Calculus/`: 向量微積分

## 如何使用

本專案使用 [Lake](https://github.com/leanprover/lake) 作為建置系統。

1.  **安裝 Lean & Lake:**
    請參考 [官方指引](https://leanprover.github.io/lean4/doc/setup.html) 安裝 `elan`，它會幫您管理 Lean 和 Lake 的版本。

2.  **下載依賴套件:**
    在專案根目錄下執行：
    ```bash
    lake exe cache get
    ```

3.  **建置專案:**
    在專案根目錄下執行：
    ```bash
    lake build
    ```

4.  **在 VS Code 中瀏覽:**
    推薦使用 Visual Studio Code 搭配 [lean4 擴充套件](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) 來瀏覽和編輯 `.lean` 檔案。
