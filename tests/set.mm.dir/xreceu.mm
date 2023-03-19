include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cxmu.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "c1.mm"
include "wss.mm"
include "ressxr.mm"
include "xrecex.mm"
include "3adant1.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "simprl.mm"
include "simpll.mm"
include "xmulcld.mm"
include "oveq1.mm"
include "ad2antll.mm"
include "simplr.mm"
include "rexrd.mm"
include "xmulass.mm"
include "syl3anc.mm"
include "xmulid2.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "3adant3.mm"
include "mpd.mm"
include "eqtr3.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3r.mm"
include "xmulcand.mm"
include "syl5ib.mm"
include "3expa.mm"
include "expcom.mm"
include "ralrimivv.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem xreceu
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. RR* /\ B e. RR /\ B =/= 0 ) -> E! x e. RR* ( B *e x ) = A )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cB
    vx
    cv
    #
    cxmu
    co
    #
    cA
    wceq
    #
    vx
    cxr
    wrex
    #
    @6
    cB
    vy
    cv
    #
    cxmu
    co
    #
    cA
    wceq
    #
    wa
    #
    @4
    @8
    wceq
    #
    wi
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    @6
    vx
    cxr
    wreu
    @3
    @9
    c1
    wceq
    #
    vy
    cxr
    wrex
    #
    @7
    cr
    cxr
    wss
    @3
    @14
    vy
    cr
    wrex
    #
    @15
    ressxr
    @1
    @2
    @16
    @0
    vy
    cB
    xrecex
    3adant1
    @14
    vy
    cr
    cxr
    ssrexv
    mpsyl
    @0
    @1
    @15
    @7
    wi
    @2
    @0
    @1
    wa
    #
    @14
    @7
    vy
    cxr
    @17
    @8
    cxr
    wcel
    #
    @14
    wa
    #
    wa
    #
    @8
    cA
    cxmu
    co
    #
    cxr
    wcel
    cB
    @21
    cxmu
    co
    #
    cA
    wceq
    #
    @7
    @20
    @8
    cA
    @17
    @18
    @14
    simprl
    #
    @0
    @1
    @19
    simpll
    #
    xmulcld
    @20
    @9
    cA
    cxmu
    co
    #
    c1
    cA
    cxmu
    co
    #
    @22
    cA
    @14
    @26
    @27
    wceq
    @17
    @18
    @9
    c1
    cA
    cxmu
    oveq1
    ad2antll
    @20
    cB
    cxr
    wcel
    @18
    @0
    @26
    @22
    wceq
    @20
    cB
    @0
    @1
    @19
    simplr
    rexrd
    @24
    @25
    cB
    @8
    cA
    xmulass
    syl3anc
    @20
    @0
    @27
    cA
    wceq
    @25
    cA
    xmulid2
    syl
    3eqtr3d
    @6
    @23
    vx
    @21
    cxr
    @4
    @21
    wceq
    @5
    @22
    cA
    @4
    @21
    cB
    cxmu
    oveq2
    eqeq1d
    rspcev
    syl2anc
    rexlimdvaa
    3adant3
    mpd
    @3
    @13
    vx
    vy
    cxr
    cxr
    @1
    @2
    @4
    cxr
    wcel
    #
    @18
    wa
    #
    @13
    wi
    @0
    @29
    @1
    @2
    wa
    #
    @13
    @28
    @18
    @30
    @13
    @11
    @5
    @9
    wceq
    @28
    @18
    @30
    w3a
    #
    @12
    @5
    @9
    cA
    eqtr3
    @31
    @4
    @8
    cB
    @28
    @18
    @30
    simp1
    @28
    @18
    @30
    simp2
    @28
    @18
    @1
    @2
    simp3l
    @28
    @18
    @1
    @2
    simp3r
    xmulcand
    syl5ib
    3expa
    expcom
    3adant1
    ralrimivv
    @6
    @10
    vx
    vy
    cxr
    @12
    @5
    @9
    cA
    @4
    @8
    cB
    cxmu
    oveq2
    eqeq1d
    reu4
    sylanbrc
end
