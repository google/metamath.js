include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "w3a.mm"
include "idlval.mm"
include "eleq2d.mm"
include "crn.mm"
include "cvv.mm"
include "c1st.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "wceq.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "syl6bb.mm"

theorem isidl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cG: class G
  let cH: class H
  let cI: class I
  let cX: class X
  let cZ: class Z
  let vr: setvar r
  let vi: setvar i
  assume idlval.1: |- G = ( 1st ` R )
  assume idlval.2: |- H = ( 2nd ` R )
  assume idlval.3: |- X = ran G
  assume idlval.4: |- Z = ( GId ` G )

  disjoint R x
  disjoint R y
  disjoint R z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint R r
  disjoint R i
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint X r
  disjoint X i
  disjoint I i
  disjoint Z r
  disjoint Z i
  disjoint G r
  disjoint G i
  disjoint H r
  disjoint H i
  assert |- ( R e. RingOps -> ( I e. ( Idl ` R ) <-> ( I C_ X /\ Z e. I /\ A. x e. I ( A. y e. I ( x G y ) e. I /\ A. z e. X ( ( z H x ) e. I /\ ( x H z ) e. I ) ) ) ) )

  proof
    cR
    crngo
    wcel
    #
    cI
    cR
    cidl
    cfv
    #
    wcel
    cI
    cZ
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
    cG
    co
    #
    @2
    wcel
    #
    vy
    @2
    wral
    #
    vz
    cv
    #
    @4
    cH
    co
    #
    @2
    wcel
    #
    @4
    @8
    cH
    co
    #
    @2
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
    @2
    wral
    #
    wa
    #
    vi
    cX
    cpw
    #
    crab
    #
    wcel
    #
    cI
    cX
    wss
    #
    cZ
    cI
    wcel
    #
    @5
    cI
    wcel
    #
    vy
    cI
    wral
    #
    @9
    cI
    wcel
    #
    @11
    cI
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
    cI
    wral
    #
    w3a
    #
    @0
    @1
    @19
    cI
    vx
    vy
    vz
    cR
    vi
    cG
    cH
    cX
    cZ
    idlval.1
    idlval.2
    idlval.3
    idlval.4
    idlval
    eleq2d
    cI
    @18
    wcel
    #
    @22
    @30
    wa
    #
    wa
    @21
    @33
    wa
    @20
    @31
    @32
    @21
    @33
    cI
    cX
    cX
    cG
    crn
    cvv
    idlval.3
    cG
    cG
    cR
    c1st
    cfv
    cvv
    idlval.1
    cR
    c1st
    fvex
    eqeltri
    rnex
    eqeltri
    elpw2
    anbi1i
    @17
    @33
    vi
    cI
    @18
    @2
    cI
    wceq
    #
    @3
    @22
    @16
    @30
    @2
    cI
    cZ
    eleq2
    @15
    @29
    vx
    @2
    cI
    @34
    @7
    @24
    @14
    @28
    @6
    @23
    vy
    @2
    cI
    @2
    cI
    @5
    eleq2
    raleqbi1dv
    @34
    @13
    @27
    vz
    cX
    @34
    @10
    @25
    @12
    @26
    @2
    cI
    @9
    eleq2
    @2
    cI
    @11
    eleq2
    anbi12d
    ralbidv
    anbi12d
    raleqbi1dv
    anbi12d
    elrab
    @21
    @22
    @30
    3anass
    3bitr4i
    syl6bb
end
