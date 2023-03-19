include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "cplusg.mm"
include "cfv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cmgm.mm"
include "wceq.mm"
include "cvv.mm"
include "fvexd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "wa.mm"
include "adantr.mm"
include "simplr.mm"
include "oveq.mm"
include "adantl.mm"
include "eleq12d.mm"
include "raleqbidv.mm"
include "sbcied2.mm"
include "df-mgm.mm"
include "elab2g.mm"

theorem ismgm
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cM: class M
  let cV: class V
  let c.op: class .o.
  let vb: setvar b
  let vm: setvar m
  let vo: setvar o
  assume ismgm.b: |- B = ( Base ` M )
  assume ismgm.o: |- .o. = ( +g ` M )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint .o. x
  disjoint .o. y
  disjoint B b
  disjoint B m
  disjoint B o
  disjoint b m
  disjoint b o
  disjoint b x
  disjoint b y
  disjoint m o
  disjoint m x
  disjoint m y
  disjoint o x
  disjoint o y
  disjoint M b
  disjoint M m
  disjoint M o
  disjoint .o. b
  disjoint .o. m
  disjoint .o. o
  assert |- ( M e. V -> ( M e. Mgm <-> A. x e. B A. y e. B ( x .o. y ) e. B ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vo
    cv
    #
    co
    #
    vb
    cv
    #
    wcel
    #
    vy
    @4
    wral
    #
    vx
    @4
    wral
    #
    vo
    vm
    cv
    #
    cplusg
    cfv
    #
    wsbc
    #
    vb
    @8
    cbs
    cfv
    #
    wsbc
    @0
    @1
    c.op
    co
    #
    cB
    wcel
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    vm
    cM
    cmgm
    cV
    @8
    cM
    wceq
    #
    @10
    @15
    vb
    @11
    cB
    cvv
    @16
    @8
    cbs
    fvexd
    @16
    @11
    cM
    cbs
    cfv
    cB
    @8
    cM
    cbs
    fveq2
    ismgm.b
    syl6eqr
    @16
    @4
    cB
    wceq
    #
    wa
    #
    @7
    @15
    vo
    @9
    c.op
    cvv
    @18
    @8
    cplusg
    fvexd
    @18
    @9
    cM
    cplusg
    cfv
    #
    c.op
    @16
    @9
    @19
    wceq
    @17
    @8
    cM
    cplusg
    fveq2
    adantr
    ismgm.o
    syl6eqr
    @18
    @2
    c.op
    wceq
    #
    wa
    #
    @6
    @14
    vx
    @4
    cB
    @16
    @17
    @20
    simplr
    #
    @21
    @5
    @13
    vy
    @4
    cB
    @22
    @21
    @3
    @12
    @4
    cB
    @20
    @3
    @12
    wceq
    @18
    @0
    @1
    @2
    c.op
    oveq
    adantl
    @22
    eleq12d
    raleqbidv
    raleqbidv
    sbcied2
    sbcied2
    vx
    vy
    vm
    vo
    vb
    df-mgm
    elab2g
end
