include "dfid3.mm"

theorem dfid2
  let vx: setvar x


  assert |- _I = { <. x , x >. | x = x }

  proof
    vx
    vx
    dfid3
end
