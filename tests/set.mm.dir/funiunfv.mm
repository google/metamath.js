include "wfun.mm"
include "cres.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "crn.mm"
include "cuni.mm"
include "cima.mm"
include "wfn.mm"
include "wceq.mm"
include "funres.mm"
include "funfn.mm"
include "sylib.mm"
include "fniunfv.mm"
include "syl.mm"
include "cdif.mm"
include "cun.mm"
include "undif2.mm"
include "wss.mm"
include "cin.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "eqtri.mm"
include "iuneq1.mm"
include "ax-mp.mm"
include "iunxun.mm"
include "c0.mm"
include "wcel.mm"
include "wn.mm"
include "eldifn.mm"
include "ndmfv.mm"
include "iuneq2i.mm"
include "iun0.mm"
include "uneq2i.mm"
include "un0.mm"
include "fvres.mm"
include "3eqtr3ri.mm"
include "df-ima.mm"
include "unieqi.mm"
include "3eqtr4g.mm"

theorem funiunfv
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint F y
  assert |- ( Fun F -> U_ x e. A ( F ` x ) = U. ( F " A ) )

  proof
    cF
    wfun
    #
    vx
    cF
    cA
    cres
    #
    cdm
    #
    vx
    cv
    #
    @1
    cfv
    #
    ciun
    #
    @1
    crn
    #
    cuni
    #
    vx
    cA
    @3
    cF
    cfv
    #
    ciun
    #
    cF
    cA
    cima
    #
    cuni
    @0
    @1
    @2
    wfn
    #
    @5
    @7
    wceq
    @0
    @1
    wfun
    @11
    cA
    cF
    funres
    @1
    funfn
    sylib
    vx
    @2
    @1
    fniunfv
    syl
    vx
    @2
    cA
    @2
    cdif
    #
    cun
    #
    @4
    ciun
    #
    vx
    cA
    @4
    ciun
    #
    @5
    @9
    @13
    cA
    wceq
    @14
    @15
    wceq
    @13
    @2
    cA
    cun
    #
    cA
    @2
    cA
    undif2
    @2
    cA
    wss
    @16
    cA
    wceq
    @2
    cA
    cF
    cdm
    #
    cin
    cA
    cF
    cA
    dmres
    cA
    @17
    inss1
    eqsstri
    @2
    cA
    ssequn1
    mpbi
    eqtri
    vx
    @13
    cA
    @4
    iuneq1
    ax-mp
    @14
    @5
    vx
    @12
    @4
    ciun
    #
    cun
    #
    @5
    vx
    @2
    @12
    @4
    iunxun
    @19
    @5
    c0
    cun
    @5
    @18
    c0
    @5
    @18
    vx
    @12
    c0
    ciun
    c0
    vx
    @12
    @4
    c0
    @3
    @12
    wcel
    @3
    @2
    wcel
    wn
    @4
    c0
    wceq
    @3
    cA
    @2
    eldifn
    @3
    @1
    ndmfv
    syl
    iuneq2i
    vx
    @12
    iun0
    eqtri
    uneq2i
    @5
    un0
    eqtri
    eqtri
    vx
    cA
    @4
    @8
    @3
    cA
    cF
    fvres
    iuneq2i
    3eqtr3ri
    @10
    @6
    cF
    cA
    df-ima
    unieqi
    3eqtr4g
end
