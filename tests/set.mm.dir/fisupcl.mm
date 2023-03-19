include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "csup.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "crio.mm"
include "simpl.mm"
include "supval2.mm"
include "wreu.mm"
include "wceq.mm"
include "simpr3.mm"
include "breq2.mm"
include "rspcev.mm"
include "ex.mm"
include "ralrimivw.mm"
include "a1d.mm"
include "anim2d.mm"
include "rgen.mm"
include "a1i.mm"
include "soss.mm"
include "sylc.mm"
include "simpr1.mm"
include "simpr2.mm"
include "fisupg.mm"
include "syl3anc.mm"
include "fisup2g.mm"
include "ssrexv.mm"
include "supeu.mm"
include "riotass2.mm"
include "syl22anc.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "eqeltrd.mm"

theorem fisupcl
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( R Or A /\ ( B e. Fin /\ B =/= (/) /\ B C_ A ) ) -> sup ( B , A , R ) e. B )

  proof
    cA
    cR
    wor
    #
    cB
    cfn
    wcel
    #
    cB
    c0
    wne
    #
    cB
    cA
    wss
    #
    w3a
    #
    wa
    #
    cB
    cA
    cR
    csup
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    wn
    vy
    cB
    wral
    #
    @7
    @6
    cR
    wbr
    #
    @7
    vz
    cv
    #
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    crio
    #
    cB
    @5
    vx
    vy
    vz
    cA
    cB
    cR
    @0
    @4
    simpl
    #
    supval2
    @5
    @8
    @13
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    crio
    #
    @16
    cB
    @5
    @3
    @19
    @15
    wi
    #
    vx
    cB
    wral
    #
    @19
    vx
    cB
    wrex
    #
    @15
    vx
    cA
    wreu
    @20
    @16
    wceq
    @0
    @1
    @2
    @3
    simpr3
    #
    @22
    @5
    @21
    vx
    cB
    @6
    cB
    wcel
    #
    @18
    @14
    @8
    @25
    @14
    @18
    @25
    @13
    vy
    cA
    @25
    @9
    @12
    @11
    @9
    vz
    @6
    cB
    @10
    @6
    @7
    cR
    breq2
    rspcev
    ex
    ralrimivw
    a1d
    anim2d
    rgen
    a1i
    @5
    cB
    cR
    wor
    #
    @1
    @2
    @23
    @5
    @3
    @0
    @26
    @24
    @17
    cB
    cA
    cR
    soss
    sylc
    #
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    vx
    vy
    vz
    cB
    cR
    fisupg
    syl3anc
    #
    @5
    vx
    vy
    vz
    cA
    cB
    cR
    @17
    @5
    @3
    @15
    vx
    cB
    wrex
    @15
    vx
    cA
    wrex
    @24
    vx
    vy
    vz
    cA
    cB
    cR
    fisup2g
    @15
    vx
    cB
    cA
    ssrexv
    sylc
    supeu
    @19
    @15
    vx
    cB
    cA
    riotass2
    syl22anc
    @5
    @19
    vx
    cB
    wreu
    @20
    cB
    wcel
    @5
    vx
    vy
    vz
    cB
    cB
    cR
    @27
    @28
    supeu
    @19
    vx
    cB
    riotacl
    syl
    eqeltrrd
    eqeltrd
end
