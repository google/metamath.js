include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cgi.mm"
include "wcel.mm"
include "co.mm"
include "wral.mm"
include "c2nd.mm"
include "wa.mm"
include "crn.mm"
include "cpw.mm"
include "crab.mm"
include "crngo.mm"
include "cidl.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "pweqd.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "oveqd.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "df-idl.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt.mm"

theorem idlval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let vi: setvar i
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let vr: setvar r
  let cI: class I
  assume idlval.1: |- G = ( 1st ` R )
  assume idlval.2: |- H = ( 2nd ` R )
  assume idlval.3: |- X = ran G
  assume idlval.4: |- Z = ( GId ` G )

  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R i
  disjoint x y
  disjoint x z
  disjoint i x
  disjoint y z
  disjoint i y
  disjoint i z
  disjoint X z
  disjoint X i
  disjoint Z i
  disjoint G i
  disjoint H i
  disjoint R r
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint i r
  disjoint X r
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint I i
  disjoint Z r
  disjoint G r
  disjoint H r
  assert |- ( R e. RingOps -> ( Idl ` R ) = { i e. ~P X | ( Z e. i /\ A. x e. i ( A. y e. i ( x G y ) e. i /\ A. z e. X ( ( z H x ) e. i /\ ( x H z ) e. i ) ) ) } )

  proof
    vr
    cR
    vr
    cv
    #
    c1st
    cfv
    #
    cgi
    cfv
    #
    vi
    cv
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    @1
    co
    #
    @3
    wcel
    #
    vy
    @3
    wral
    #
    vz
    cv
    #
    @5
    @0
    c2nd
    cfv
    #
    co
    #
    @3
    wcel
    #
    @5
    @10
    @11
    co
    #
    @3
    wcel
    #
    wa
    #
    vz
    @1
    crn
    #
    wral
    #
    wa
    #
    vx
    @3
    wral
    #
    wa
    #
    vi
    @17
    cpw
    #
    crab
    cZ
    @3
    wcel
    #
    @5
    @6
    cG
    co
    #
    @3
    wcel
    #
    vy
    @3
    wral
    #
    @10
    @5
    cH
    co
    #
    @3
    wcel
    #
    @5
    @10
    cH
    co
    #
    @3
    wcel
    #
    wa
    #
    vz
    cX
    wral
    #
    wa
    #
    vx
    @3
    wral
    #
    wa
    #
    vi
    cX
    cpw
    #
    crab
    crngo
    cidl
    @0
    cR
    wceq
    #
    @21
    @35
    vi
    @22
    @36
    @37
    @17
    cX
    @37
    @17
    cG
    crn
    #
    cX
    @37
    @1
    cG
    @37
    @1
    cR
    c1st
    cfv
    #
    cG
    @0
    cR
    c1st
    fveq2
    idlval.1
    syl6eqr
    #
    rneqd
    idlval.3
    syl6eqr
    #
    pweqd
    @37
    @4
    @23
    @20
    @34
    @37
    @2
    cZ
    @3
    @37
    @2
    cG
    cgi
    cfv
    cZ
    @37
    @1
    cG
    cgi
    @40
    fveq2d
    idlval.4
    syl6eqr
    eleq1d
    @37
    @19
    @33
    vx
    @3
    @37
    @9
    @26
    @18
    @32
    @37
    @8
    @25
    vy
    @3
    @37
    @7
    @24
    @3
    @37
    @1
    cG
    @5
    @6
    @40
    oveqd
    eleq1d
    ralbidv
    @37
    @16
    @31
    vz
    @17
    cX
    @41
    @37
    @13
    @28
    @15
    @30
    @37
    @12
    @27
    @3
    @37
    @11
    cH
    @10
    @5
    @37
    @11
    cR
    c2nd
    cfv
    cH
    @0
    cR
    c2nd
    fveq2
    idlval.2
    syl6eqr
    #
    oveqd
    eleq1d
    @37
    @14
    @29
    @3
    @37
    @11
    cH
    @5
    @10
    @42
    oveqd
    eleq1d
    anbi12d
    raleqbidv
    anbi12d
    ralbidv
    anbi12d
    rabeqbidv
    vx
    vy
    vz
    vi
    vr
    df-idl
    @35
    vi
    @36
    cX
    cX
    @38
    cvv
    idlval.3
    cG
    cG
    @39
    cvv
    idlval.1
    cR
    c1st
    fvex
    eqeltri
    rnex
    eqeltri
    pwex
    rabex
    fvmpt
end
