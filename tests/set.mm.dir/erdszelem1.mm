include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cpw.mm"
include "wcel.mm"
include "cima.mm"
include "clt.mm"
include "cres.mm"
include "wiso.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "ovex.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "reseq2.mm"
include "isoeq1.mm"
include "syl.mm"
include "isoeq4.mm"
include "imaeq2.mm"
include "isoeq5.mm"
include "3bitrd.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem erdszelem1
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cF: class F
  let cO: class O
  let cX: class X
  let vx: setvar x
  assume erdszelem1.1: |- S = { y e. ~P ( 1 ... A ) | ( ( F |` y ) Isom < , O ( y , ( F " y ) ) /\ A e. y ) }

  disjoint A y
  disjoint F y
  disjoint O y
  disjoint X y
  disjoint x y
  disjoint A x
  disjoint S x
  assert |- ( X e. S <-> ( X C_ ( 1 ... A ) /\ ( F |` X ) Isom < , O ( X , ( F " X ) ) /\ A e. X ) )

  proof
    cX
    c1
    cA
    cfz
    co
    #
    cpw
    #
    wcel
    #
    cX
    cF
    cX
    cima
    #
    clt
    cO
    cF
    cX
    cres
    #
    wiso
    #
    cA
    cX
    wcel
    #
    wa
    #
    wa
    cX
    @0
    wss
    #
    @7
    wa
    cX
    cS
    wcel
    @8
    @5
    @6
    w3a
    @2
    @8
    @7
    cX
    @0
    c1
    cA
    cfz
    ovex
    elpw2
    anbi1i
    vy
    cv
    #
    cF
    @9
    cima
    #
    clt
    cO
    cF
    @9
    cres
    #
    wiso
    #
    cA
    @9
    wcel
    #
    wa
    @7
    vy
    cX
    @1
    cS
    @9
    cX
    wceq
    #
    @12
    @5
    @13
    @6
    @14
    @12
    @9
    @10
    clt
    cO
    @4
    wiso
    #
    cX
    @10
    clt
    cO
    @4
    wiso
    #
    @5
    @14
    @11
    @4
    wceq
    @12
    @15
    wb
    @9
    cX
    cF
    reseq2
    @9
    @10
    clt
    cO
    @4
    @11
    isoeq1
    syl
    @9
    @10
    cX
    clt
    cO
    @4
    isoeq4
    @14
    @10
    @3
    wceq
    @16
    @5
    wb
    @9
    cX
    cF
    imaeq2
    cX
    @10
    @3
    clt
    cO
    @4
    isoeq5
    syl
    3bitrd
    @9
    cX
    cA
    eleq2
    anbi12d
    erdszelem1.1
    elrab2
    @8
    @5
    @6
    3anass
    3bitr4i
end
