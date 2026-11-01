(ns kata)

(defn points [games]
  (reduce + (map (fn [game] 
         (let [x (int (first game))
               y (int (last game))]
           (cond (> x y) 3
                 (== x y) 1
                 :else 0))) games)))