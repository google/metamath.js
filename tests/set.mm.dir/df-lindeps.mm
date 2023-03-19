
axiom df-lindeps
  let vm: setvar m
  let vs: setvar s
  assert |- linDepS = { <. s , m >. | -. s linIndS m }
end
