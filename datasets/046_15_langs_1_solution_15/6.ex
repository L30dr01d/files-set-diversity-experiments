defmodule TotalPoints do
  def points(games) do
    games
    |> Enum.map(&String.split(&1, ":"))
    |> Enum.map(&to_integers/1)
    |> Enum.map(&score/1)
    |> Enum.sum()
  end

  defp score([x, y]) when x > y, do: 3
  defp score([x, y]) when x < y, do: 0
  defp score([x, y]) when x == y, do: 1

  defp to_integers(list) do
    Enum.map(list, &String.to_integer/1)
  end
end