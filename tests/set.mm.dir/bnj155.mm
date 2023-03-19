include "cv.mm"
include "wsbc.mm"
include "csuc.mm"
include "c1o.mm"
include "wcel.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "sbcbii.mm"
include "vex.mm"
include "weq.mm"
include "fveq1.mm"
include "iuneq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "sbcie.mm"
include "3bitri.mm"

theorem bnj155
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let bnjwpsm: wff ps'
  let bnjwps1: wff ps1
  assume bnj155.1: |- ( ps1 <-> [. g / f ]. ps' )
  assume bnj155.2: |- ( ps' <-> A. i e. _om ( suc i e. 1o -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )

  disjoint A f
  disjoint R f
  disjoint f g
  disjoint f i
  disjoint f y
  disjoint g i
  disjoint g y
  disjoint i y
  assert |- ( ps1 <-> A. i e. _om ( suc i e. 1o -> ( g ` suc i ) = U_ y e. ( g ` i ) _pred ( y , A , R ) ) )

  proof
    bnjwps1
    bnjwpsm
    vf
    vg
    cv
    #
    wsbc
    vi
    cv
    #
    csuc
    #
    c1o
    wcel
    #
    @2
    vf
    cv
    #
    cfv
    #
    vy
    @1
    @4
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
    wi
    #
    vi
    com
    wral
    #
    vf
    @0
    wsbc
    @3
    @2
    @0
    cfv
    #
    vy
    @1
    @0
    cfv
    #
    @7
    ciun
    #
    wceq
    #
    wi
    #
    vi
    com
    wral
    #
    bnj155.1
    bnjwpsm
    @11
    vf
    @0
    bnj155.2
    sbcbii
    @11
    @17
    vf
    @0
    vg
    vex
    vf
    vg
    weq
    #
    @10
    @16
    vi
    com
    @18
    @9
    @15
    @3
    @18
    @5
    @12
    @8
    @14
    @2
    @4
    @0
    fveq1
    @18
    vy
    @6
    @13
    @7
    @1
    @4
    @0
    fveq1
    iuneq1d
    eqeq12d
    imbi2d
    ralbidv
    sbcie
    3bitri
end
