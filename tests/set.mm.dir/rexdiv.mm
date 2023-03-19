include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "crio.mm"
include "cc.mm"
include "cxdiv.mm"
include "cdiv.mm"
include "wrex.mm"
include "wreu.mm"
include "redivcl.mm"
include "recn.mm"
include "id.mm"
include "3anim123i.mm"
include "divcan2.mm"
include "syl.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "receu.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "ax-resscn.mm"
include "rgenw.mm"
include "riotass2.mm"
include "mpanl12.mm"
include "cxmu.mm"
include "cxr.mm"
include "rexr.mm"
include "xdivval.mm"
include "syl3an1.mm"
include "ressxr.mm"
include "a1i.mm"
include "rexmul.mm"
include "biimprd.mm"
include "ralrimiva.mm"
include "3ad2ant2.mm"
include "xreceu.mm"
include "syl22anc.mm"
include "eqtr4d.mm"
include "divval.mm"
include "3eqtr4d.mm"

theorem rexdiv
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR /\ B =/= 0 ) -> ( A /e B ) = ( A / B ) )

  proof
    cA
    cr
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
    cmul
    co
    #
    cA
    wceq
    #
    vx
    cr
    crio
    #
    @6
    vx
    cc
    crio
    #
    cA
    cB
    cxdiv
    co
    #
    cA
    cB
    cdiv
    co
    #
    @3
    @6
    vx
    cr
    wrex
    #
    @6
    vx
    cc
    wreu
    #
    @7
    @8
    wceq
    #
    @3
    @10
    cr
    wcel
    cB
    @10
    cmul
    co
    #
    cA
    wceq
    #
    @11
    cA
    cB
    redivcl
    @3
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @2
    w3a
    #
    @15
    @0
    @16
    @1
    @17
    @2
    @2
    cA
    recn
    cB
    recn
    @2
    id
    3anim123i
    #
    cA
    cB
    divcan2
    syl
    @6
    @15
    vx
    @10
    cr
    @4
    @10
    wceq
    @5
    @14
    cA
    @4
    @10
    cB
    cmul
    oveq2
    eqeq1d
    rspcev
    syl2anc
    #
    @3
    @18
    @12
    @19
    vx
    cA
    cB
    receu
    syl
    cr
    cc
    wss
    @6
    @6
    wi
    #
    vx
    cr
    wral
    @11
    @12
    wa
    @13
    ax-resscn
    @21
    vx
    cr
    @6
    id
    rgenw
    @6
    @6
    vx
    cr
    cc
    riotass2
    mpanl12
    syl2anc
    @3
    @9
    cB
    @4
    cxmu
    co
    #
    cA
    wceq
    #
    vx
    cxr
    crio
    #
    @7
    @0
    cA
    cxr
    wcel
    #
    @1
    @2
    @9
    @24
    wceq
    cA
    rexr
    #
    vx
    cA
    cB
    xdivval
    syl3an1
    @3
    cr
    cxr
    wss
    #
    @6
    @23
    wi
    #
    vx
    cr
    wral
    #
    @11
    @23
    vx
    cxr
    wreu
    #
    @7
    @24
    wceq
    @27
    @3
    ressxr
    a1i
    @1
    @0
    @29
    @2
    @1
    @28
    vx
    cr
    @1
    @4
    cr
    wcel
    wa
    #
    @23
    @6
    @31
    @22
    @5
    cA
    cB
    @4
    rexmul
    eqeq1d
    biimprd
    ralrimiva
    3ad2ant2
    @20
    @0
    @25
    @1
    @2
    @30
    @26
    vx
    cA
    cB
    xreceu
    syl3an1
    @6
    @23
    vx
    cr
    cxr
    riotass2
    syl22anc
    eqtr4d
    @3
    @18
    @10
    @8
    wceq
    @19
    vx
    cA
    cB
    divval
    syl
    3eqtr4d
end
