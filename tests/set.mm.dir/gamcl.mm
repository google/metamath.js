include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "cgam.mm"
include "gamf.mm"
include "ffvelrni.mm"

theorem gamcl
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x


  assert |- ( A e. ( CC \ ( ZZ \ NN ) ) -> ( _G ` A ) e. CC )

  proof
    cc
    cz
    cn
    cdif
    cdif
    cc
    cA
    cgam
    gamf
    ffvelrni
end
