include "cxp.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "cvv.mm"
include "xpexr2.mm"
include "simpld.mm"
include "simprd.mm"
include "simpr.mm"
include "xpnz.mm"
include "sylibr.mm"
include "xpdom3.mm"
include "syl3anc.mm"
include "domfi.mm"
include "syldan.mm"
include "cen.mm"
include "xpcomeng.mm"
include "syl2anc.mm"
include "domentr.mm"
include "jca.mm"

theorem xpfir
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( ( A X. B ) e. Fin /\ ( A X. B ) =/= (/) ) -> ( A e. Fin /\ B e. Fin ) )

  proof
    cA
    cB
    cxp
    #
    cfn
    wcel
    #
    @0
    c0
    wne
    #
    wa
    #
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    @1
    @2
    cA
    @0
    cdom
    wbr
    #
    @4
    @3
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cB
    c0
    wne
    #
    @6
    @3
    @7
    @8
    cA
    cB
    cfn
    xpexr2
    #
    simpld
    #
    @3
    @7
    @8
    @10
    simprd
    #
    @3
    cA
    c0
    wne
    #
    @9
    @3
    @2
    @13
    @9
    wa
    @1
    @2
    simpr
    cA
    cB
    xpnz
    sylibr
    #
    simprd
    cA
    cB
    cvv
    cvv
    xpdom3
    syl3anc
    @0
    cA
    domfi
    syldan
    @1
    @2
    cB
    @0
    cdom
    wbr
    #
    @5
    @3
    cB
    cB
    cA
    cxp
    #
    cdom
    wbr
    #
    @16
    @0
    cen
    wbr
    #
    @15
    @3
    @8
    @7
    @13
    @17
    @12
    @11
    @3
    @13
    @9
    @14
    simpld
    cB
    cA
    cvv
    cvv
    xpdom3
    syl3anc
    @3
    @8
    @7
    @18
    @12
    @11
    cB
    cA
    cvv
    cvv
    xpcomeng
    syl2anc
    cB
    @16
    @0
    domentr
    syl2anc
    @0
    cB
    domfi
    syldan
    jca
end
