include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "c1.mm"
include "recex.mm"
include "3adant1.mm"
include "simprl.mm"
include "simpll.mm"
include "mulcld.mm"
include "oveq1.mm"
include "ad2antll.mm"
include "simplr.mm"
include "mulassd.mm"
include "mulid2d.mm"
include "3eqtr3d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "3adant3.mm"
include "mpd.mm"
include "eqtr3.mm"
include "mulcan.mm"
include "syl5ib.mm"
include "3expa.mm"
include "expcom.mm"
include "ralrimivv.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem receu
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> E! x e. CC ( B x. x ) = A )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
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
    cmul
    co
    #
    cA
    wceq
    #
    vx
    cc
    wrex
    #
    @6
    cB
    vy
    cv
    #
    cmul
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
    cc
    wral
    vx
    cc
    wral
    @6
    vx
    cc
    wreu
    @3
    @9
    c1
    wceq
    #
    vy
    cc
    wrex
    #
    @7
    @1
    @2
    @15
    @0
    vy
    cB
    recex
    3adant1
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
    cc
    @16
    @8
    cc
    wcel
    #
    @14
    wa
    #
    wa
    #
    @8
    cA
    cmul
    co
    #
    cc
    wcel
    cB
    @20
    cmul
    co
    #
    cA
    wceq
    #
    @7
    @19
    @8
    cA
    @16
    @17
    @14
    simprl
    #
    @0
    @1
    @18
    simpll
    #
    mulcld
    @19
    @9
    cA
    cmul
    co
    #
    c1
    cA
    cmul
    co
    #
    @21
    cA
    @14
    @25
    @26
    wceq
    @16
    @17
    @9
    c1
    cA
    cmul
    oveq1
    ad2antll
    @19
    cB
    @8
    cA
    @0
    @1
    @18
    simplr
    @23
    @24
    mulassd
    @19
    cA
    @24
    mulid2d
    3eqtr3d
    @6
    @22
    vx
    @20
    cc
    @4
    @20
    wceq
    @5
    @21
    cA
    @4
    @20
    cB
    cmul
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
    cc
    cc
    @1
    @2
    @4
    cc
    wcel
    #
    @17
    wa
    #
    @13
    wi
    @0
    @28
    @1
    @2
    wa
    #
    @13
    @27
    @17
    @29
    @13
    @11
    @5
    @9
    wceq
    @27
    @17
    @29
    w3a
    @12
    @5
    @9
    cA
    eqtr3
    @4
    @8
    cB
    mulcan
    syl5ib
    3expa
    expcom
    3adant1
    ralrimivv
    @6
    @10
    vx
    vy
    cc
    @12
    @5
    @9
    cA
    @4
    @8
    cB
    cmul
    oveq2
    eqeq1d
    reu4
    sylanbrc
end
