include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cucn.mm"
include "co.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "cuni.mm"
include "cdm.mm"
include "wral.mm"
include "wrex.mm"
include "cmap.mm"
include "crab.mm"
include "crn.mm"
include "cvv.mm"
include "wceq.mm"
include "elrnust.mm"
include "adantr.mm"
include "adantl.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "simpr.mm"
include "unieqd.mm"
include "dmeqd.mm"
include "simpl.mm"
include "oveq12d.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "rexeqbidv.mm"
include "rabeqbidv.mm"
include "df-ucn.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"
include "ustbas2.mm"
include "oveqan12rd.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "eqtr4d.mm"

theorem ucnval
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let vf: setvar f
  let cV: class V
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vr: setvar r
  let vu: setvar u
  let vv: setvar v

  disjoint f r
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint U f
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint U r
  disjoint s x
  disjoint s y
  disjoint U s
  disjoint x y
  disjoint U x
  disjoint U y
  disjoint V f
  disjoint V r
  disjoint V s
  disjoint V x
  disjoint X f
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y r
  disjoint Y s
  disjoint Y x
  disjoint f u
  disjoint f v
  disjoint r u
  disjoint r v
  disjoint s u
  disjoint s v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint U u
  disjoint v x
  disjoint v y
  disjoint U v
  disjoint V u
  disjoint V v
  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. ( UnifOn ` Y ) ) -> ( U uCn V ) = { f e. ( Y ^m X ) | A. s e. V E. r e. U A. x e. X A. y e. X ( x r y -> ( f ` x ) s ( f ` y ) ) } )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cV
    cY
    cust
    cfv
    wcel
    #
    wa
    #
    cU
    cV
    cucn
    co
    #
    vx
    cv
    #
    vy
    cv
    #
    vr
    cv
    wbr
    @4
    vf
    cv
    #
    cfv
    @5
    @6
    cfv
    vs
    cv
    wbr
    wi
    #
    vy
    cU
    cuni
    #
    cdm
    #
    wral
    #
    vx
    @9
    wral
    #
    vr
    cU
    wrex
    #
    vs
    cV
    wral
    #
    vf
    cV
    cuni
    #
    cdm
    #
    @9
    cmap
    co
    #
    crab
    #
    @7
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    vr
    cU
    wrex
    #
    vs
    cV
    wral
    #
    vf
    cY
    cX
    cmap
    co
    #
    crab
    @2
    cU
    cust
    crn
    cuni
    #
    wcel
    #
    cV
    @23
    wcel
    #
    @17
    cvv
    wcel
    #
    @3
    @17
    wceq
    @0
    @24
    @1
    cU
    cX
    elrnust
    adantr
    @1
    @25
    @0
    cV
    cY
    elrnust
    adantl
    @26
    @2
    @13
    vf
    @16
    @15
    @9
    cmap
    ovex
    rabex
    a1i
    vu
    vv
    cU
    cV
    @23
    @23
    @7
    vy
    vu
    cv
    #
    cuni
    #
    cdm
    #
    wral
    #
    vx
    @29
    wral
    #
    vr
    @27
    wrex
    #
    vs
    vv
    cv
    #
    wral
    #
    vf
    @33
    cuni
    #
    cdm
    #
    @29
    cmap
    co
    #
    crab
    @17
    cucn
    cvv
    @27
    cU
    wceq
    #
    @33
    cV
    wceq
    #
    wa
    #
    @34
    @13
    vf
    @37
    @16
    @40
    @36
    @15
    @29
    @9
    cmap
    @40
    @35
    @14
    @40
    @33
    cV
    @38
    @39
    simpr
    #
    unieqd
    dmeqd
    @40
    @28
    @8
    @40
    @27
    cU
    @38
    @39
    simpl
    #
    unieqd
    dmeqd
    #
    oveq12d
    @40
    @32
    @12
    vs
    @33
    cV
    @41
    @40
    @31
    @11
    vr
    @27
    cU
    @42
    @40
    @30
    @10
    vx
    @29
    @9
    @43
    @40
    @7
    vy
    @29
    @9
    @43
    raleqdv
    raleqbidv
    rexeqbidv
    raleqbidv
    rabeqbidv
    vx
    vy
    vv
    vu
    vf
    vs
    vr
    df-ucn
    ovmpt2ga
    syl3anc
    @2
    @21
    @13
    vf
    @22
    @16
    @1
    @0
    cY
    @15
    cX
    @9
    cmap
    cV
    cY
    ustbas2
    cU
    cX
    ustbas2
    #
    oveqan12rd
    @2
    @20
    @12
    vs
    cV
    @2
    @19
    @11
    vr
    cU
    @2
    @18
    @10
    vx
    cX
    @9
    @0
    cX
    @9
    wceq
    @1
    @44
    adantr
    #
    @2
    @7
    vy
    cX
    @9
    @45
    raleqdv
    raleqbidv
    rexbidv
    ralbidv
    rabeqbidv
    eqtr4d
end
