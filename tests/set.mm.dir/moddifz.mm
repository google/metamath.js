include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cz.mm"
include "moddiffl.mm"
include "rerpdivcl.mm"
include "flcld.mm"
include "eqeltrd.mm"

theorem moddifz
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( A - ( A mod B ) ) / B ) e. ZZ )

  proof
    cA
    cr
    wcel
    cB
    crp
    wcel
    wa
    #
    cA
    cA
    cB
    cmo
    co
    cmin
    co
    cB
    cdiv
    co
    cA
    cB
    cdiv
    co
    #
    cfl
    cfv
    cz
    cA
    cB
    moddiffl
    @0
    @1
    cA
    cB
    rerpdivcl
    flcld
    eqeltrd
end
