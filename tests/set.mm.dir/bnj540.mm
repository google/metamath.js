include "wsbc.mm"
include "cv.mm"
include "csuc.mm"
include "wcel.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "sbcbii.mm"
include "bnj538.mm"
include "cvv.mm"
include "wb.mm"
include "sbcimg.mm"
include "ax-mp.mm"
include "ralbii.mm"
include "3bitri.mm"
include "bnj525.mm"
include "fveq1.mm"
include "bnj1113.mm"
include "eqeq12d.mm"
include "sbcie.mm"
include "imbi12i.mm"

theorem bnj540
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let cG: class G
  let cN: class N
  let bnjwpsn: wff ps"
  assume bnj540.1: |- ( ps <-> A. i e. _om ( suc i e. N -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj540.2: |- ( ps" <-> [. G / f ]. ps )
  assume bnj540.3: |- G e. _V

  disjoint A f
  disjoint G f
  disjoint G i
  disjoint G y
  disjoint f i
  disjoint f y
  disjoint i y
  disjoint N f
  disjoint R f
  assert |- ( ps" <-> A. i e. _om ( suc i e. N -> ( G ` suc i ) = U_ y e. ( G ` i ) _pred ( y , A , R ) ) )

  proof
    bnjwpsn
    wps
    vf
    cG
    wsbc
    #
    vi
    cv
    #
    csuc
    #
    cN
    wcel
    #
    vf
    cG
    wsbc
    #
    @2
    vf
    cv
    #
    cfv
    #
    vy
    @1
    @5
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    #
    wceq
    #
    vf
    cG
    wsbc
    #
    wi
    #
    vi
    com
    wral
    #
    @3
    @2
    cG
    cfv
    #
    vy
    @1
    cG
    cfv
    #
    @8
    ciun
    #
    wceq
    #
    wi
    #
    vi
    com
    wral
    bnj540.2
    @0
    @3
    @10
    wi
    #
    vi
    com
    wral
    #
    vf
    cG
    wsbc
    @19
    vf
    cG
    wsbc
    #
    vi
    com
    wral
    @13
    wps
    @20
    vf
    cG
    bnj540.1
    sbcbii
    @19
    vi
    vf
    cG
    com
    bnj540.3
    bnj538
    @21
    @12
    vi
    com
    cG
    cvv
    wcel
    @21
    @12
    wb
    bnj540.3
    @3
    @10
    vf
    cG
    cvv
    sbcimg
    ax-mp
    ralbii
    3bitri
    @12
    @18
    vi
    com
    @4
    @3
    @11
    @17
    @3
    vf
    cG
    bnj540.3
    bnj525
    @10
    @17
    vf
    cG
    bnj540.3
    @5
    cG
    wceq
    @6
    @14
    @9
    @16
    @2
    @5
    cG
    fveq1
    vy
    @5
    cG
    @7
    @15
    @8
    @1
    @5
    cG
    fveq1
    bnj1113
    eqeq12d
    sbcie
    imbi12i
    ralbii
    3bitri
end
