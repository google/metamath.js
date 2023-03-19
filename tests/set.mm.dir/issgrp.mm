include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cplusg.mm"
include "cfv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cmgm.mm"
include "csgrp.mm"
include "cvv.mm"
include "fvexd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "wa.mm"
include "adantr.mm"
include "simplr.mm"
include "wb.mm"
include "id.mm"
include "oveq.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "raleqbidv.mm"
include "sbcied2.mm"
include "df-sgrp.mm"
include "elrab2.mm"

theorem issgrp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cM: class M
  let c.op: class .o.
  let vb: setvar b
  let vg: setvar g
  let vo: setvar o
  assume issgrp.b: |- B = ( Base ` M )
  assume issgrp.o: |- .o. = ( +g ` M )

  disjoint B x
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint .o. x
  disjoint .o. y
  disjoint .o. z
  disjoint B b
  disjoint B g
  disjoint B o
  disjoint b g
  disjoint b o
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint g o
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint M b
  disjoint M g
  disjoint M o
  disjoint .o. b
  disjoint .o. g
  disjoint .o. o
  assert |- ( M e. SGrp <-> ( M e. Mgm /\ A. x e. B A. y e. B A. z e. B ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) ) )

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
    vz
    cv
    #
    @2
    co
    #
    @0
    @1
    @4
    @2
    co
    #
    @2
    co
    #
    wceq
    #
    vz
    vb
    cv
    #
    wral
    #
    vy
    @9
    wral
    #
    vx
    @9
    wral
    #
    vo
    vg
    cv
    #
    cplusg
    cfv
    #
    wsbc
    #
    vb
    @13
    cbs
    cfv
    #
    wsbc
    @0
    @1
    c.op
    co
    #
    @4
    c.op
    co
    #
    @0
    @1
    @4
    c.op
    co
    #
    c.op
    co
    #
    wceq
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    vg
    cM
    cmgm
    csgrp
    @13
    cM
    wceq
    #
    @15
    @24
    vb
    @16
    cB
    cvv
    @25
    @13
    cbs
    fvexd
    @25
    @16
    cM
    cbs
    cfv
    cB
    @13
    cM
    cbs
    fveq2
    issgrp.b
    syl6eqr
    @25
    @9
    cB
    wceq
    #
    wa
    #
    @12
    @24
    vo
    @14
    c.op
    cvv
    @27
    @13
    cplusg
    fvexd
    @27
    @14
    cM
    cplusg
    cfv
    #
    c.op
    @25
    @14
    @28
    wceq
    @26
    @13
    cM
    cplusg
    fveq2
    adantr
    issgrp.o
    syl6eqr
    @27
    @2
    c.op
    wceq
    #
    wa
    #
    @11
    @23
    vx
    @9
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
    @9
    cB
    @31
    @30
    @8
    @21
    vz
    @9
    cB
    @31
    @29
    @8
    @21
    wb
    @27
    @29
    @5
    @18
    @7
    @20
    @29
    @3
    @17
    @4
    @4
    @2
    c.op
    @29
    id
    #
    @0
    @1
    @2
    c.op
    oveq
    @29
    @4
    eqidd
    oveq123d
    @29
    @0
    @0
    @6
    @19
    @2
    c.op
    @32
    @29
    @0
    eqidd
    @1
    @4
    @2
    c.op
    oveq
    oveq123d
    eqeq12d
    adantl
    raleqbidv
    raleqbidv
    raleqbidv
    sbcied2
    sbcied2
    vx
    vy
    vz
    vg
    vo
    vb
    df-sgrp
    elrab2
end
