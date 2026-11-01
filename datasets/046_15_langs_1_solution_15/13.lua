local kata = {}

function kata.points(games)
  local total_points = 0

    for i = 1, #games do
        local x, y = games[i]:match("(%d):(%d)")
        x = tonumber(x)
        y = tonumber(y)

        if x > y then
            total_points = total_points + 3
        elseif x == y then
            total_points = total_points + 1
        else
            total_points = total_points + 0
        end
    end

    return total_points
end

return kata