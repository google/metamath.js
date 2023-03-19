include "cxr.mm"
include "cmnf.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "wcel.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "icossxr.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "wa.mm"
include "clt.mm"
include "w3a.mm"
include "wb.mm"
include "mnfxr.mm"
include "simpl.mm"
include "elico1.mm"
include "sylancr.mm"
include "simpr.mm"
include "mnfle.mm"
include "jccir.mm"
include "biantrurd.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "xrltnle.mm"
include "ancoms.mm"
include "3bitr2d.mm"
include "rabbi2dva.mm"
include "syl5eqr.mm"
include "mpteq2ia.mm"
include "rneqi.mm"
include "eqtri.mm"

theorem leordtvallem2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z
  assume leordtval.1: |- A = ran ( x e. RR* |-> ( x (,] +oo ) )
  assume leordtval.2: |- B = ran ( x e. RR* |-> ( -oo [,) x ) )

  disjoint x y
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  assert |- B = ran ( x e. RR* |-> { y e. RR* | -. x <_ y } )

  proof
    cB
    vx
    cxr
    cmnf
    vx
    cv
    #
    cico
    co
    #
    cmpt
    #
    crn
    vx
    cxr
    @0
    vy
    cv
    #
    cle
    wbr
    wn
    #
    vy
    cxr
    crab
    #
    cmpt
    #
    crn
    leordtval.2
    @2
    @6
    vx
    cxr
    @1
    @5
    @0
    cxr
    wcel
    #
    @1
    cxr
    @1
    cin
    #
    @5
    @1
    cxr
    wss
    @8
    @1
    wceq
    cmnf
    @0
    icossxr
    @1
    cxr
    sseqin2
    mpbi
    @7
    @4
    vy
    cxr
    @1
    @7
    @3
    cxr
    wcel
    #
    wa
    #
    @3
    @1
    wcel
    #
    @9
    cmnf
    @3
    cle
    wbr
    #
    @3
    @0
    clt
    wbr
    #
    w3a
    #
    @13
    @4
    @10
    cmnf
    cxr
    wcel
    @7
    @11
    @14
    wb
    mnfxr
    @7
    @9
    simpl
    cmnf
    @0
    @3
    elico1
    sylancr
    @10
    @13
    @9
    @12
    wa
    #
    @13
    wa
    @14
    @10
    @15
    @13
    @10
    @9
    @12
    @7
    @9
    simpr
    @3
    mnfle
    jccir
    biantrurd
    @9
    @12
    @13
    df-3an
    syl6bbr
    @9
    @7
    @13
    @4
    wb
    @3
    @0
    xrltnle
    ancoms
    3bitr2d
    rabbi2dva
    syl5eqr
    mpteq2ia
    rneqi
    eqtri
end
