include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "modval.mm"
include "rpre.mm"
include "adantl.mm"
include "refldivcl.mm"
include "remulcld.mm"
include "resubcl.mm"
include "syldan.mm"
include "eqeltrd.mm"

theorem modcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( A mod B ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    cB
    cmo
    co
    cA
    cB
    cA
    cB
    cdiv
    co
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cr
    cA
    cB
    modval
    @0
    @1
    @4
    cr
    wcel
    @5
    cr
    wcel
    @2
    cB
    @3
    @1
    cB
    cr
    wcel
    @0
    cB
    rpre
    adantl
    cA
    cB
    refldivcl
    remulcld
    cA
    @4
    resubcl
    syldan
    eqeltrd
end
