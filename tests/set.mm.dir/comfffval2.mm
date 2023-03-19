include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "chom.mm"
include "co.mm"
include "cmpt2.mm"
include "eqid.mm"
include "comfffval.mm"
include "wcel.mm"
include "wa.mm"
include "xp2nd.mm"
include "adantr.mm"
include "simpr.mm"
include "homfval.mm"
include "c1st.mm"
include "cop.mm"
include "xp1st.mm"
include "df-ov.mm"
include "3eqtr3g.mm"
include "wceq.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "mpt2eq3ia.mm"
include "eqtr4i.mm"

theorem comfffval2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cO: class O
  let cX: class X
  let cY: class Y
  let wph: wff ph
  let cZ: class Z
  assume comfffval2.o: |- O = ( comf ` C )
  assume comfffval2.b: |- B = ( Base ` C )
  assume comfffval2.h: |- H = ( Homf ` C )
  assume comfffval2.x: |- .x. = ( comp ` C )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint X f
  disjoint X g
  disjoint Y f
  disjoint Y g
  disjoint f ph
  disjoint g ph
  disjoint Z f
  disjoint Z g
  assert |- O = ( x e. ( B X. B ) , y e. B |-> ( g e. ( ( 2nd ` x ) H y ) , f e. ( H ` x ) |-> ( g ( x .x. y ) f ) ) )

  proof
    cO
    vx
    vy
    cB
    cB
    cxp
    #
    cB
    vg
    vf
    vx
    cv
    #
    c2nd
    cfv
    #
    vy
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    @1
    @4
    cfv
    #
    vg
    cv
    vf
    cv
    @1
    @3
    c.x
    co
    co
    #
    cmpt2
    #
    cmpt2
    vx
    vy
    @0
    cB
    vg
    vf
    @2
    @3
    cH
    co
    #
    @1
    cH
    cfv
    #
    @7
    cmpt2
    #
    cmpt2
    vx
    vy
    cB
    cC
    c.x
    vf
    vg
    @4
    cO
    comfffval2.o
    comfffval2.b
    @4
    eqid
    #
    comfffval2.x
    comfffval
    vx
    vy
    @0
    cB
    @11
    @8
    @1
    @0
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    #
    vg
    vf
    @9
    @10
    @7
    @5
    @6
    @7
    @15
    cB
    cC
    cH
    @4
    @2
    @3
    comfffval2.h
    comfffval2.b
    @12
    @13
    @2
    cB
    wcel
    @14
    @1
    cB
    cB
    xp2nd
    adantr
    #
    @13
    @14
    simpr
    homfval
    @15
    @1
    c1st
    cfv
    #
    @2
    cop
    #
    cH
    cfv
    #
    @18
    @4
    cfv
    #
    @10
    @6
    @15
    @17
    @2
    cH
    co
    @17
    @2
    @4
    co
    @19
    @20
    @15
    cB
    cC
    cH
    @4
    @17
    @2
    comfffval2.h
    comfffval2.b
    @12
    @13
    @17
    cB
    wcel
    @14
    @1
    cB
    cB
    xp1st
    adantr
    @16
    homfval
    @17
    @2
    cH
    df-ov
    @17
    @2
    @4
    df-ov
    3eqtr3g
    @15
    @1
    @18
    cH
    @13
    @1
    @18
    wceq
    @14
    @1
    cB
    cB
    1st2nd2
    adantr
    #
    fveq2d
    @15
    @1
    @18
    @4
    @21
    fveq2d
    3eqtr4d
    @15
    @7
    eqidd
    mpt2eq123dv
    mpt2eq3ia
    eqtr4i
end
