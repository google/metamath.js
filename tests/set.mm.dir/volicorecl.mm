include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cc0.mm"
include "cif.mm"
include "volico.mm"
include "simpr.mm"
include "simpl.mm"
include "resubcld.mm"
include "0red.mm"
include "ifcld.mm"
include "eqeltrd.mm"

theorem volicorecl
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR ) -> ( vol ` ( A [,) B ) ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cico
    co
    cvol
    cfv
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    cmin
    co
    #
    cc0
    cif
    cr
    cA
    cB
    volico
    @2
    @3
    @4
    cc0
    cr
    @2
    cB
    cA
    @0
    @1
    simpr
    @0
    @1
    simpl
    resubcld
    @2
    0red
    ifcld
    eqeltrd
end
