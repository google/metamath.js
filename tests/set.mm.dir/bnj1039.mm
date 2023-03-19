include "cv.mm"
include "wsbc.mm"
include "csuc.mm"
include "wcel.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "nfra1.mm"
include "nfxfr.mm"
include "sbcgf.mm"
include "ax-mp.mm"
include "3bitri.mm"

theorem bnj1039
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let bnjwpsm: wff ps'
  assume bnj1039.1: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1039.2: |- ( ps' <-> [. j / i ]. ps )


  assert |- ( ps' <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )

  proof
    bnjwpsm
    wps
    vi
    vj
    cv
    #
    wsbc
    #
    wps
    vi
    cv
    #
    csuc
    #
    vn
    cv
    wcel
    @3
    vf
    cv
    #
    cfv
    vy
    @2
    @4
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    wceq
    wi
    #
    vi
    com
    wral
    #
    bnj1039.2
    @0
    cvv
    wcel
    @1
    wps
    wb
    vj
    vex
    wps
    vi
    @0
    cvv
    wps
    @6
    vi
    bnj1039.1
    @5
    vi
    com
    nfra1
    nfxfr
    sbcgf
    ax-mp
    bnj1039.1
    3bitri
end
