include "cdmn.mm"
include "wcel.mm"
include "ccring.mm"
include "crngo.mm"
include "dmncrng.mm"
include "crngorngo.mm"
include "syl.mm"

theorem dmnrngo
  let cR: class R


  assert |- ( R e. Dmn -> R e. RingOps )

  proof
    cR
    cdmn
    wcel
    cR
    ccring
    wcel
    cR
    crngo
    wcel
    cR
    dmncrng
    cR
    crngorngo
    syl
end
