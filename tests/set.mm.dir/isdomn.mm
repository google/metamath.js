include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "c0g.mm"
include "wsbc.mm"
include "cbs.mm"
include "cnzr.mm"
include "cdomn.mm"
include "cvv.mm"
include "fvexd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "wa.mm"
include "adantr.mm"
include "simplr.mm"
include "oveqdr.mm"
include "id.mm"
include "eqeqan12d.mm"
include "wb.mm"
include "eqeq2.mm"
include "orbi12d.mm"
include "adantl.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "sbcied2.mm"
include "df-domn.mm"
include "elrab2.mm"

theorem isdomn
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.0: class .0.
  let vb: setvar b
  let vr: setvar r
  let vz: setvar z
  assume isdomn.b: |- B = ( Base ` R )
  assume isdomn.t: |- .x. = ( .r ` R )
  assume isdomn.z: |- .0. = ( 0g ` R )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint .0. x
  disjoint .0. y
  disjoint B b
  disjoint B r
  disjoint B z
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint x z
  disjoint y z
  disjoint R b
  disjoint R r
  disjoint R z
  disjoint .x. b
  disjoint .x. r
  disjoint .x. z
  disjoint .0. b
  disjoint .0. r
  disjoint .0. z
  assert |- ( R e. Domn <-> ( R e. NzRing /\ A. x e. B A. y e. B ( ( x .x. y ) = .0. -> ( x = .0. \/ y = .0. ) ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vr
    cv
    #
    cmulr
    cfv
    #
    co
    #
    vz
    cv
    #
    wceq
    #
    @0
    @5
    wceq
    #
    @1
    @5
    wceq
    #
    wo
    #
    wi
    #
    vy
    vb
    cv
    #
    wral
    #
    vx
    @11
    wral
    #
    vz
    @2
    c0g
    cfv
    #
    wsbc
    #
    vb
    @2
    cbs
    cfv
    #
    wsbc
    @0
    @1
    c.x
    co
    #
    c.0
    wceq
    #
    @0
    c.0
    wceq
    #
    @1
    c.0
    wceq
    #
    wo
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    vr
    cR
    cnzr
    cdomn
    @2
    cR
    wceq
    #
    @15
    @24
    vb
    @16
    cB
    cvv
    @25
    @2
    cbs
    fvexd
    @25
    @16
    cR
    cbs
    cfv
    cB
    @2
    cR
    cbs
    fveq2
    isdomn.b
    syl6eqr
    @25
    @11
    cB
    wceq
    #
    wa
    #
    @13
    @24
    vz
    @14
    c.0
    cvv
    @27
    @2
    c0g
    fvexd
    @27
    @14
    cR
    c0g
    cfv
    #
    c.0
    @25
    @14
    @28
    wceq
    @26
    @2
    cR
    c0g
    fveq2
    adantr
    isdomn.z
    syl6eqr
    @27
    @5
    c.0
    wceq
    #
    wa
    #
    @12
    @23
    vx
    @11
    cB
    @25
    @26
    @29
    simplr
    #
    @30
    @10
    @22
    vy
    @11
    cB
    @31
    @30
    @6
    @18
    @9
    @21
    @27
    @29
    @4
    @17
    @5
    c.0
    @25
    @26
    vx
    vy
    @3
    c.x
    @25
    @3
    cR
    cmulr
    cfv
    c.x
    @2
    cR
    cmulr
    fveq2
    isdomn.t
    syl6eqr
    oveqdr
    @29
    id
    eqeqan12d
    @29
    @9
    @21
    wb
    @27
    @29
    @7
    @19
    @8
    @20
    @5
    c.0
    @0
    eqeq2
    @5
    c.0
    @1
    eqeq2
    orbi12d
    adantl
    imbi12d
    raleqbidv
    raleqbidv
    sbcied2
    sbcied2
    vx
    vy
    vz
    vr
    vb
    df-domn
    elrab2
end
