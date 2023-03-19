include "cmgmhm.mm"
include "co.mm"
include "wcel.mm"
include "cmgm.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "mgmhmrcl.mm"
include "cmap.mm"
include "crab.mm"
include "cplusg.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqan12rd.mm"
include "adantr.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "eqeqan12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "df-mgmhm.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"
include "biadan2.mm"

theorem ismgmhm
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  let cS: class S
  let cT: class T
  let cF: class F
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vk: setvar k
  assume ismgmhm.b: |- B = ( Base ` S )
  assume ismgmhm.c: |- C = ( Base ` T )
  assume ismgmhm.p: |- .+ = ( +g ` S )
  assume ismgmhm.q: |- .+^ = ( +g ` T )

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
  disjoint C f
  disjoint C s
  disjoint C t
  disjoint F f
  disjoint k x
  assert |- ( F e. ( S MgmHom T ) <-> ( ( S e. Mgm /\ T e. Mgm ) /\ ( F : B --> C /\ A. x e. B A. y e. B ( F ` ( x .+ y ) ) = ( ( F ` x ) .+^ ( F ` y ) ) ) ) )

  proof
    cF
    cS
    cT
    cmgmhm
    co
    #
    wcel
    #
    cS
    cmgm
    wcel
    cT
    cmgm
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
    wa
    #
    cS
    cT
    cF
    mgmhmrcl
    @2
    @1
    cF
    @6
    vf
    cv
    #
    cfv
    #
    @4
    @14
    cfv
    #
    @5
    @14
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
    #
    vx
    cB
    wral
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
    @13
    @2
    @0
    @23
    cF
    vs
    vt
    cS
    cT
    cmgm
    cmgm
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
    @14
    cfv
    #
    @16
    @17
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
    @25
    cbs
    cfv
    #
    wral
    #
    vx
    @33
    wral
    #
    vf
    @29
    cbs
    cfv
    #
    @33
    cmap
    co
    #
    crab
    @23
    cmgmhm
    @25
    cS
    wceq
    #
    @29
    cT
    wceq
    #
    wa
    #
    @35
    @21
    vf
    @37
    @22
    @39
    @38
    @36
    cC
    @33
    cB
    cmap
    @39
    @36
    cT
    cbs
    cfv
    #
    cC
    @29
    cT
    cbs
    fveq2
    ismgmhm.c
    syl6eqr
    @38
    @33
    cS
    cbs
    cfv
    #
    cB
    @25
    cS
    cbs
    fveq2
    ismgmhm.b
    syl6eqr
    #
    oveqan12rd
    @40
    @34
    @20
    vx
    @33
    cB
    @38
    @33
    cB
    wceq
    @39
    @43
    adantr
    #
    @40
    @32
    @19
    vy
    @33
    cB
    @44
    @38
    @39
    @28
    @15
    @31
    @18
    @38
    @27
    @6
    @14
    @38
    @26
    c.pl
    @4
    @5
    @38
    @26
    cS
    cplusg
    cfv
    c.pl
    @25
    cS
    cplusg
    fveq2
    ismgmhm.p
    syl6eqr
    oveqd
    fveq2d
    @39
    @30
    c.pd
    @16
    @17
    @39
    @30
    cT
    cplusg
    cfv
    c.pd
    @29
    cT
    cplusg
    fveq2
    ismgmhm.q
    syl6eqr
    oveqd
    eqeqan12d
    raleqbidv
    raleqbidv
    rabeqbidv
    vx
    vy
    vt
    vf
    vs
    df-mgmhm
    @21
    vf
    @22
    cC
    cB
    cmap
    ovex
    rabex
    ovmpt2a
    eleq2d
    @24
    cF
    @22
    wcel
    #
    @12
    wa
    @13
    @21
    @12
    vf
    cF
    @22
    @14
    cF
    wceq
    #
    @19
    @11
    vx
    vy
    cB
    cB
    @46
    @15
    @7
    @18
    @10
    @6
    @14
    cF
    fveq1
    @46
    @16
    @8
    @17
    @9
    c.pd
    @4
    @14
    cF
    fveq1
    @5
    @14
    cF
    fveq1
    oveq12d
    eqeq12d
    2ralbidv
    elrab
    @45
    @3
    @12
    cC
    cB
    cF
    cC
    @41
    cvv
    ismgmhm.c
    cT
    cbs
    fvex
    eqeltri
    cB
    @42
    cvv
    ismgmhm.b
    cS
    cbs
    fvex
    eqeltri
    elmap
    anbi1i
    bitri
    syl6bb
    biadan2
end
