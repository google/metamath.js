include "cxr.mm"
include "cv.mm"
include "cpnf.mm"
include "cioc.mm"
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
include "iocssxr.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "wa.mm"
include "clt.mm"
include "w3a.mm"
include "wb.mm"
include "simpl.mm"
include "pnfxr.mm"
include "elioc1.mm"
include "sylancl.mm"
include "simpr.mm"
include "pnfge.mm"
include "jccir.mm"
include "biantrurd.mm"
include "3anan32.mm"
include "syl6bbr.mm"
include "xrltnle.mm"
include "3bitr2d.mm"
include "rabbi2dva.mm"
include "syl5eqr.mm"
include "mpteq2ia.mm"
include "rneqi.mm"
include "eqtri.mm"

theorem leordtvallem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  assume leordtval.1: |- A = ran ( x e. RR* |-> ( x (,] +oo ) )

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
  assert |- A = ran ( x e. RR* |-> { y e. RR* | -. y <_ x } )

  proof
    cA
    vx
    cxr
    vx
    cv
    #
    cpnf
    cioc
    co
    #
    cmpt
    #
    crn
    vx
    cxr
    vy
    cv
    #
    @0
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
    leordtval.1
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
    @0
    cpnf
    iocssxr
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
    @0
    @3
    clt
    wbr
    #
    @3
    cpnf
    cle
    wbr
    #
    w3a
    #
    @12
    @4
    @10
    @7
    cpnf
    cxr
    wcel
    @11
    @14
    wb
    @7
    @9
    simpl
    pnfxr
    @0
    cpnf
    @3
    elioc1
    sylancl
    @10
    @12
    @9
    @13
    wa
    #
    @12
    wa
    @14
    @10
    @15
    @12
    @10
    @9
    @13
    @7
    @9
    simpr
    @3
    pnfge
    jccir
    biantrurd
    @9
    @12
    @13
    3anan32
    syl6bbr
    @0
    @3
    xrltnle
    3bitr2d
    rabbi2dva
    syl5eqr
    mpteq2ia
    rneqi
    eqtri
end
