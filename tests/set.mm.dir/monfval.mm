include "cmon.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cop.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "crab.mm"
include "cmpt2.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "chom.mm"
include "cco.mm"
include "csb.mm"
include "cvv.mm"
include "fvexd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "wa.mm"
include "simpl.mm"
include "fveq2d.mm"
include "simplr.mm"
include "simpr.mm"
include "oveqd.mm"
include "simpll.mm"
include "mpteq12dv.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "mpt2eq123dv.mm"
include "csbied2.mm"
include "df-mon.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem monfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cM: class M
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h
  let cG: class G
  let cK: class K
  let cF: class F
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ismon.b: |- B = ( Base ` C )
  assume ismon.h: |- H = ( Hom ` C )
  assume ismon.o: |- .x. = ( comp ` C )
  assume ismon.s: |- M = ( Mono ` C )
  assume ismon.c: |- ( ph -> C e. Cat )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint M f
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint f h
  disjoint g h
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint G g
  disjoint G h
  disjoint G z
  disjoint K g
  disjoint K h
  disjoint K z
  disjoint h ph
  disjoint C b
  disjoint C c
  disjoint C h
  disjoint H b
  disjoint H c
  disjoint H h
  disjoint .x. b
  disjoint .x. c
  disjoint .x. h
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F z
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y g
  disjoint Y h
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z g
  disjoint Z h
  disjoint Z z
  assert |- ( ph -> M = ( x e. B , y e. B |-> { f e. ( x H y ) | A. z e. B Fun `' ( g e. ( z H x ) |-> ( f ( <. z , x >. .x. y ) g ) ) } ) )

  proof
    wph
    cM
    cC
    cmon
    cfv
    #
    vx
    vy
    cB
    cB
    vg
    vz
    cv
    #
    vx
    cv
    #
    cH
    co
    #
    vf
    cv
    #
    vg
    cv
    #
    @1
    @2
    cop
    #
    vy
    cv
    #
    c.x
    co
    #
    co
    #
    cmpt
    #
    ccnv
    #
    wfun
    #
    vz
    cB
    wral
    #
    vf
    @2
    @7
    cH
    co
    #
    crab
    #
    cmpt2
    #
    ismon.s
    wph
    cC
    ccat
    wcel
    @0
    @16
    wceq
    ismon.c
    vc
    cC
    vb
    vc
    cv
    #
    cbs
    cfv
    #
    vh
    @17
    chom
    cfv
    #
    vx
    vy
    vb
    cv
    #
    @20
    vg
    @1
    @2
    vh
    cv
    #
    co
    #
    @4
    @5
    @6
    @7
    @17
    cco
    cfv
    #
    co
    #
    co
    #
    cmpt
    #
    ccnv
    #
    wfun
    #
    vz
    @20
    wral
    #
    vf
    @2
    @7
    @21
    co
    #
    crab
    #
    cmpt2
    #
    csb
    #
    csb
    @16
    ccat
    cmon
    @17
    cC
    wceq
    #
    vb
    @18
    cB
    @33
    @16
    cvv
    @34
    @17
    cbs
    fvexd
    @34
    @18
    cC
    cbs
    cfv
    #
    cB
    @17
    cC
    cbs
    fveq2
    ismon.b
    syl6eqr
    @34
    @20
    cB
    wceq
    #
    wa
    #
    vh
    @19
    cH
    @32
    @16
    cvv
    @37
    @17
    chom
    fvexd
    @37
    @19
    cC
    chom
    cfv
    cH
    @37
    @17
    cC
    chom
    @34
    @36
    simpl
    fveq2d
    ismon.h
    syl6eqr
    @37
    @21
    cH
    wceq
    #
    wa
    #
    vx
    vy
    @20
    @20
    @31
    cB
    cB
    @15
    @34
    @36
    @38
    simplr
    #
    @40
    @39
    @29
    @13
    vf
    @30
    @14
    @39
    @21
    cH
    @2
    @7
    @37
    @38
    simpr
    #
    oveqd
    @39
    @28
    @12
    vz
    @20
    cB
    @40
    @39
    @27
    @11
    @39
    @26
    @10
    @39
    vg
    @22
    @25
    @3
    @9
    @39
    @21
    cH
    @1
    @2
    @41
    oveqd
    @39
    @24
    @8
    @4
    @5
    @39
    @23
    c.x
    @6
    @7
    @39
    @23
    cC
    cco
    cfv
    c.x
    @39
    @17
    cC
    cco
    @34
    @36
    @38
    simpll
    fveq2d
    ismon.o
    syl6eqr
    oveqd
    oveqd
    mpteq12dv
    cnveqd
    funeqd
    raleqbidv
    rabeqbidv
    mpt2eq123dv
    csbied2
    csbied2
    vx
    vy
    vz
    vf
    vg
    vh
    vb
    vc
    df-mon
    vx
    vy
    cB
    cB
    @15
    cB
    @35
    cvv
    ismon.b
    cC
    cbs
    fvex
    eqeltri
    #
    @42
    mpt2ex
    fvmpt
    syl
    syl5eq
end
