include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "cmnd.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cplusg.mm"
include "cbs.mm"
include "c0g.mm"
include "cmap.mm"
include "crab.mm"
include "df-mhm.mm"
include "elmpt2cl.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqan12rd.mm"
include "adantr.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "eqeqan12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "eleq2d.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "anbi1i.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "syl6bb.mm"
include "biadan2.mm"

theorem ismhm
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  let cS: class S
  let cT: class T
  let cF: class F
  let cY: class Y
  let c.0: class .0.
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  assume ismhm.b: |- B = ( Base ` S )
  assume ismhm.c: |- C = ( Base ` T )
  assume ismhm.p: |- .+ = ( +g ` S )
  assume ismhm.q: |- .+^ = ( +g ` T )
  assume ismhm.z: |- .0. = ( 0g ` S )
  assume ismhm.y: |- Y = ( 0g ` T )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint F x
  disjoint F y
  disjoint f s
  disjoint f t
  disjoint .+^ f
  disjoint s t
  disjoint .+^ s
  disjoint .+^ t
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint s x
  disjoint s y
  disjoint B s
  disjoint t x
  disjoint t y
  disjoint B t
  disjoint S f
  disjoint S s
  disjoint S t
  disjoint T f
  disjoint T s
  disjoint T t
  disjoint .+ f
  disjoint .+ s
  disjoint .+ t
  disjoint .0. f
  disjoint .0. s
  disjoint .0. t
  disjoint C f
  disjoint C s
  disjoint C t
  disjoint F f
  disjoint Y f
  disjoint Y s
  disjoint Y t
  assert |- ( F e. ( S MndHom T ) <-> ( ( S e. Mnd /\ T e. Mnd ) /\ ( F : B --> C /\ A. x e. B A. y e. B ( F ` ( x .+ y ) ) = ( ( F ` x ) .+^ ( F ` y ) ) /\ ( F ` .0. ) = Y ) ) )

  proof
    cF
    cS
    cT
    cmhm
    co
    #
    wcel
    #
    cS
    cmnd
    wcel
    cT
    cmnd
    wcel
    wa
    #
    cB
    cC
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    c.0
    cF
    cfv
    #
    cY
    wceq
    #
    w3a
    #
    vs
    vt
    cmnd
    cmnd
    @4
    @5
    vs
    cv
    #
    cplusg
    cfv
    #
    co
    #
    vf
    cv
    #
    cfv
    #
    @4
    @19
    cfv
    #
    @5
    @19
    cfv
    #
    vt
    cv
    #
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    @16
    cbs
    cfv
    #
    wral
    #
    vx
    @27
    wral
    #
    @16
    c0g
    cfv
    #
    @19
    cfv
    #
    @23
    c0g
    cfv
    #
    wceq
    #
    wa
    #
    vf
    @23
    cbs
    cfv
    #
    @27
    cmap
    co
    #
    crab
    #
    cS
    cT
    cmhm
    cF
    vx
    vy
    vt
    vf
    vs
    df-mhm
    #
    elmpt2cl
    @2
    @1
    cF
    @6
    @19
    cfv
    #
    @21
    @22
    c.pd
    co
    #
    wceq
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    c.0
    @19
    cfv
    #
    cY
    wceq
    #
    wa
    #
    vf
    cC
    cB
    cmap
    co
    #
    crab
    #
    wcel
    #
    @15
    @2
    @0
    @48
    cF
    vs
    vt
    cS
    cT
    cmnd
    cmnd
    @37
    @48
    cmhm
    @16
    cS
    wceq
    #
    @23
    cT
    wceq
    #
    wa
    #
    @34
    @46
    vf
    @36
    @47
    @51
    @50
    @35
    cC
    @27
    cB
    cmap
    @51
    @35
    cT
    cbs
    cfv
    #
    cC
    @23
    cT
    cbs
    fveq2
    ismhm.c
    syl6eqr
    @50
    @27
    cS
    cbs
    cfv
    #
    cB
    @16
    cS
    cbs
    fveq2
    ismhm.b
    syl6eqr
    #
    oveqan12rd
    @52
    @29
    @43
    @33
    @45
    @52
    @28
    @42
    vx
    @27
    cB
    @50
    @27
    cB
    wceq
    @51
    @55
    adantr
    #
    @52
    @26
    @41
    vy
    @27
    cB
    @56
    @50
    @51
    @20
    @39
    @25
    @40
    @50
    @18
    @6
    @19
    @50
    @17
    c.pl
    @4
    @5
    @50
    @17
    cS
    cplusg
    cfv
    c.pl
    @16
    cS
    cplusg
    fveq2
    ismhm.p
    syl6eqr
    oveqd
    fveq2d
    @51
    @24
    c.pd
    @21
    @22
    @51
    @24
    cT
    cplusg
    cfv
    c.pd
    @23
    cT
    cplusg
    fveq2
    ismhm.q
    syl6eqr
    oveqd
    eqeqan12d
    raleqbidv
    raleqbidv
    @50
    @51
    @31
    @44
    @32
    cY
    @50
    @30
    c.0
    @19
    @50
    @30
    cS
    c0g
    cfv
    c.0
    @16
    cS
    c0g
    fveq2
    ismhm.z
    syl6eqr
    fveq2d
    @51
    @32
    cT
    c0g
    cfv
    cY
    @23
    cT
    c0g
    fveq2
    ismhm.y
    syl6eqr
    eqeqan12d
    anbi12d
    rabeqbidv
    @38
    @46
    vf
    @47
    cC
    cB
    cmap
    ovex
    rabex
    ovmpt2a
    eleq2d
    cF
    @47
    wcel
    #
    @12
    @14
    wa
    #
    wa
    @3
    @58
    wa
    @49
    @15
    @57
    @3
    @58
    cC
    cB
    cF
    cC
    @53
    cvv
    ismhm.c
    cT
    cbs
    fvex
    eqeltri
    cB
    @54
    cvv
    ismhm.b
    cS
    cbs
    fvex
    eqeltri
    elmap
    anbi1i
    @46
    @58
    vf
    cF
    @47
    @19
    cF
    wceq
    #
    @43
    @12
    @45
    @14
    @59
    @41
    @11
    vx
    vy
    cB
    cB
    @59
    @39
    @7
    @40
    @10
    @6
    @19
    cF
    fveq1
    @59
    @21
    @8
    @22
    @9
    c.pd
    @4
    @19
    cF
    fveq1
    @5
    @19
    cF
    fveq1
    oveq12d
    eqeq12d
    2ralbidv
    @59
    @44
    @13
    cY
    c.0
    @19
    cF
    fveq1
    eqeq1d
    anbi12d
    elrab
    @3
    @12
    @14
    3anass
    3bitr4i
    syl6bb
    biadan2
end
