include "cc.mm"
include "ce.mm"
include "eff.mm"
include "ffvelrni.mm"

theorem efcl
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x


  assert |- ( A e. CC -> ( exp ` A ) e. CC )

  proof
    cc
    cc
    cA
    ce
    eff
    ffvelrni
end
