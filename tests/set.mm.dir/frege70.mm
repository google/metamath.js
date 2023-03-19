include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "wb.mm"
include "dffrege69.mm"
include "wsbc.mm"
include "frege68c.mm"
include "sbcel1v.mm"
include "biimpri.mm"
include "sbcim1.mm"
include "sbcal.mm"
include "csb.mm"
include "sbcbr1g.mm"
include "ax-mp.mm"
include "wceq.mm"
include "csbvarg.mm"
include "breq1i.mm"
include "bitri.mm"
include "sbcg.mm"
include "3imtr3g.mm"
include "alimi.mm"
include "sylbi.mm"
include "syl56.mm"
include "syl6.mm"

theorem frege70
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume frege70.x: |- X e. V

  disjoint A y
  disjoint R y
  disjoint X y
  disjoint x y
  disjoint A x
  disjoint R x
  assert |- ( R hereditary A -> ( X e. A -> A. y ( X R y -> y e. A ) ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    @0
    vy
    cv
    #
    cR
    wbr
    #
    @2
    cA
    wcel
    #
    wi
    #
    vy
    wal
    #
    wi
    #
    vx
    wal
    cA
    cR
    whe
    #
    wb
    #
    @8
    cX
    cA
    wcel
    #
    cX
    @2
    cR
    wbr
    #
    @4
    wi
    #
    vy
    wal
    #
    wi
    #
    wi
    vx
    vy
    cA
    cR
    dffrege69
    @9
    @8
    @7
    vx
    cX
    wsbc
    #
    @14
    @7
    @8
    vx
    cX
    cV
    frege70.x
    frege68c
    @10
    @1
    vx
    cX
    wsbc
    #
    @15
    @6
    vx
    cX
    wsbc
    #
    @13
    @16
    @10
    vx
    cX
    cA
    sbcel1v
    biimpri
    @1
    @6
    vx
    cX
    sbcim1
    @17
    @5
    vx
    cX
    wsbc
    #
    vy
    wal
    @13
    @5
    vy
    vx
    cX
    sbcal
    @18
    @12
    vy
    @18
    @3
    vx
    cX
    wsbc
    #
    @4
    vx
    cX
    wsbc
    #
    @11
    @4
    @3
    @4
    vx
    cX
    sbcim1
    @19
    vx
    cX
    @0
    csb
    #
    @2
    cR
    wbr
    #
    @11
    cX
    cV
    wcel
    #
    @19
    @22
    wb
    frege70.x
    vx
    cX
    @0
    @2
    cR
    cV
    sbcbr1g
    ax-mp
    @21
    cX
    @2
    cR
    @23
    @21
    cX
    wceq
    frege70.x
    vx
    cX
    cV
    csbvarg
    ax-mp
    breq1i
    bitri
    @23
    @20
    @4
    wb
    frege70.x
    @4
    vx
    cX
    cV
    sbcg
    ax-mp
    3imtr3g
    alimi
    sylbi
    syl56
    syl6
    ax-mp
end
