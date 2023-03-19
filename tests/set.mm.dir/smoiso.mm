include "cep.mm"
include "wiso.mm"
include "word.mm"
include "con0.mm"
include "wss.mm"
include "w3a.mm"
include "cdm.mm"
include "wf.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wsmo.mm"
include "wf1o.mm"
include "isof1o.mm"
include "f1of.mm"
include "syl.mm"
include "ffdm.mm"
include "simpld.mm"
include "fss.mm"
include "sylan.mm"
include "3adant2.mm"
include "syl3an1.mm"
include "wceq.mm"
include "wb.mm"
include "fdm.mm"
include "eqcomd.mm"
include "ordeq.mm"
include "4syl.mm"
include "biimpa.mm"
include "3adant3.mm"
include "wa.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "3syl.mm"
include "wbr.mm"
include "isorel.mm"
include "epel.mm"
include "fvex.mm"
include "epelc.mm"
include "3bitr3g.mm"
include "biimpd.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "3ad2ant1.mm"
include "df-smo.mm"
include "syl3anbrc.mm"

theorem smoiso
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- ( ( F Isom _E , _E ( A , B ) /\ Ord A /\ B C_ On ) -> Smo F )

  proof
    cA
    cB
    cep
    cep
    cF
    wiso
    #
    cA
    word
    #
    cB
    con0
    wss
    #
    w3a
    cF
    cdm
    #
    con0
    cF
    wf
    #
    @3
    word
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    wcel
    #
    wi
    #
    vy
    @3
    wral
    vx
    @3
    wral
    #
    cF
    wsmo
    @0
    cA
    cB
    cF
    wf
    #
    @1
    @2
    @4
    @0
    cA
    cB
    cF
    wf1o
    #
    @14
    cA
    cB
    cep
    cep
    cF
    isof1o
    #
    cA
    cB
    cF
    f1of
    #
    syl
    @14
    @2
    @4
    @1
    @14
    @3
    cB
    cF
    wf
    #
    @2
    @4
    @14
    @18
    @3
    cA
    wss
    cA
    cB
    cF
    ffdm
    simpld
    @3
    cB
    con0
    cF
    fss
    sylan
    3adant2
    syl3an1
    @0
    @1
    @5
    @2
    @0
    @1
    @5
    @0
    @15
    @14
    cA
    @3
    wceq
    @1
    @5
    wb
    @16
    @17
    @14
    @3
    cA
    cA
    cB
    cF
    fdm
    #
    eqcomd
    cA
    @3
    ordeq
    4syl
    biimpa
    3adant3
    @0
    @1
    @13
    @2
    @0
    @12
    vx
    vy
    @3
    @3
    @0
    @6
    @3
    wcel
    #
    @7
    @3
    wcel
    #
    wa
    #
    @6
    cA
    wcel
    #
    @7
    cA
    wcel
    #
    wa
    #
    @12
    @0
    @15
    @14
    @22
    @25
    wb
    @16
    @17
    @14
    @20
    @23
    @21
    @24
    @14
    @3
    cA
    @6
    @19
    eleq2d
    @14
    @3
    cA
    @7
    @19
    eleq2d
    anbi12d
    3syl
    @0
    @25
    @12
    @0
    @25
    wa
    #
    @8
    @11
    @26
    @6
    @7
    cep
    wbr
    @9
    @10
    cep
    wbr
    @8
    @11
    cA
    cB
    @6
    @7
    cep
    cep
    cF
    isorel
    vx
    vy
    epel
    @9
    @10
    @7
    cF
    fvex
    epelc
    3bitr3g
    biimpd
    ex
    sylbid
    ralrimivv
    3ad2ant1
    vx
    vy
    cF
    df-smo
    syl3anbrc
end
