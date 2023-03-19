include "word.mm"
include "con0.mm"
include "wss.mm"
include "wa.mm"
include "wfo.mm"
include "wsmo.mm"
include "cep.mm"
include "wiso.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wf1.mm"
include "wf.mm"
include "fof.mm"
include "smo11.mm"
include "sylan.mm"
include "simpl.mm"
include "df-f1o.mm"
include "sylanbrc.mm"
include "adantl.mm"
include "wfn.mm"
include "fofn.mm"
include "wcel.mm"
include "smoord.mm"
include "epel.mm"
include "fvex.mm"
include "epelc.mm"
include "3bitr4g.mm"
include "ralrimivva.mm"
include "df-isom.mm"
include "ex.mm"
include "w3a.mm"
include "isof1o.mm"
include "f1ofo.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "smoiso.mm"
include "jca.mm"
include "3expib.mm"
include "com12.mm"
include "impbid.mm"

theorem smoiso2
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Ord A /\ B C_ On ) -> ( ( F : A -onto-> B /\ Smo F ) <-> F Isom _E , _E ( A , B ) ) )

  proof
    cA
    word
    #
    cB
    con0
    wss
    #
    wa
    #
    cA
    cB
    cF
    wfo
    #
    cF
    wsmo
    #
    wa
    #
    cA
    cB
    cep
    cep
    cF
    wiso
    #
    @2
    @5
    @6
    @2
    @5
    wa
    cA
    cB
    cF
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cep
    wbr
    #
    @8
    cF
    cfv
    #
    @9
    cF
    cfv
    #
    cep
    wbr
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @6
    @5
    @7
    @2
    @5
    cA
    cB
    cF
    wf1
    #
    @3
    @7
    @3
    cA
    cB
    cF
    wf
    @4
    @16
    cA
    cB
    cF
    fof
    cA
    cB
    cF
    smo11
    sylan
    @3
    @4
    simpl
    cA
    cB
    cF
    df-f1o
    sylanbrc
    adantl
    @5
    @15
    @2
    @3
    cF
    cA
    wfn
    #
    @4
    @15
    cA
    cB
    cF
    fofn
    @17
    @4
    wa
    #
    @14
    vx
    vy
    cA
    cA
    @18
    @8
    cA
    wcel
    @9
    cA
    wcel
    wa
    wa
    @8
    @9
    wcel
    @11
    @12
    wcel
    @10
    @13
    cA
    @8
    @9
    cF
    smoord
    vx
    vy
    epel
    @11
    @12
    @9
    cF
    fvex
    epelc
    3bitr4g
    ralrimivva
    sylan
    adantl
    vx
    vy
    cA
    cB
    cep
    cep
    cF
    df-isom
    sylanbrc
    ex
    @6
    @2
    @5
    @6
    @0
    @1
    @5
    @6
    @0
    @1
    w3a
    @3
    @4
    @6
    @0
    @3
    @1
    @6
    @7
    @3
    cA
    cB
    cep
    cep
    cF
    isof1o
    cA
    cB
    cF
    f1ofo
    syl
    3ad2ant1
    cA
    cB
    cF
    smoiso
    jca
    3expib
    com12
    impbid
end
