include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "rerpdivcl.mm"
include "reflcl.mm"
include "syl.mm"

theorem refldivcl
  let cK: class K
  let cL: class L


  assert |- ( ( K e. RR /\ L e. RR+ ) -> ( |_ ` ( K / L ) ) e. RR )

  proof
    cK
    cr
    wcel
    cL
    crp
    wcel
    wa
    cK
    cL
    cdiv
    co
    #
    cr
    wcel
    @0
    cfl
    cfv
    cr
    wcel
    cK
    cL
    rerpdivcl
    @0
    reflcl
    syl
end
