include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "crab.mm"
include "wa.mm"
include "cvv.mm"
include "monfval.mm"
include "wceq.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "opeq2d.mm"
include "oveqd.mm"
include "mpteq12dv.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem ismon
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cM: class M
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cK: class K
  let cZ: class Z
  assume ismon.b: |- B = ( Base ` C )
  assume ismon.h: |- H = ( Hom ` C )
  assume ismon.o: |- .x. = ( comp ` C )
  assume ismon.s: |- M = ( Mono ` C )
  assume ismon.c: |- ( ph -> C e. Cat )
  assume ismon.x: |- ( ph -> X e. B )
  assume ismon.y: |- ( ph -> Y e. B )

  disjoint g z
  disjoint B g
  disjoint B z
  disjoint g ph
  disjoint ph z
  disjoint C g
  disjoint C z
  disjoint H g
  disjoint H z
  disjoint .x. g
  disjoint .x. z
  disjoint F g
  disjoint F z
  disjoint X g
  disjoint X z
  disjoint Y g
  disjoint Y z
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
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint G g
  disjoint G h
  disjoint G z
  disjoint K g
  disjoint K h
  disjoint K z
  disjoint f ph
  disjoint h ph
  disjoint ph x
  disjoint ph y
  disjoint C b
  disjoint C c
  disjoint C f
  disjoint C h
  disjoint C x
  disjoint C y
  disjoint H b
  disjoint H c
  disjoint H f
  disjoint H h
  disjoint H x
  disjoint H y
  disjoint .x. b
  disjoint .x. c
  disjoint .x. f
  disjoint .x. h
  disjoint .x. x
  disjoint .x. y
  disjoint F f
  disjoint F h
  disjoint X f
  disjoint X h
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y h
  disjoint Y x
  disjoint Y y
  disjoint Z g
  disjoint Z h
  disjoint Z z
  disjoint M f
  assert |- ( ph -> ( F e. ( X M Y ) <-> ( F e. ( X H Y ) /\ A. z e. B Fun `' ( g e. ( z H X ) |-> ( F ( <. z , X >. .x. Y ) g ) ) ) ) )

  proof
    wph
    cF
    cX
    cY
    cM
    co
    #
    wcel
    cF
    vg
    vz
    cv
    #
    cX
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
    cX
    cop
    #
    cY
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
    cX
    cY
    cH
    co
    #
    crab
    #
    wcel
    cF
    @12
    wcel
    vg
    @2
    cF
    @4
    @6
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
    wa
    wph
    @0
    @13
    cF
    wph
    vx
    vy
    cX
    cY
    cB
    cB
    vg
    @1
    vx
    cv
    #
    cH
    co
    #
    @3
    @4
    @1
    @19
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
    @19
    @22
    cH
    co
    #
    crab
    @13
    cM
    cvv
    wph
    vx
    vy
    vz
    cB
    cC
    c.x
    vf
    vg
    cH
    cM
    ismon.b
    ismon.h
    ismon.o
    ismon.s
    ismon.c
    monfval
    wph
    @19
    cX
    wceq
    #
    @22
    cY
    wceq
    #
    wa
    wa
    #
    @28
    @11
    vf
    @29
    @12
    @32
    @19
    cX
    @22
    cY
    cH
    wph
    @30
    @31
    simprl
    #
    wph
    @30
    @31
    simprr
    #
    oveq12d
    @32
    @27
    @10
    vz
    cB
    @32
    @26
    @9
    @32
    @25
    @8
    @32
    vg
    @20
    @24
    @2
    @7
    @32
    @19
    cX
    @1
    cH
    @33
    oveq2d
    @32
    @23
    @6
    @3
    @4
    @32
    @21
    @5
    @22
    cY
    c.x
    @32
    @19
    cX
    @1
    @33
    opeq2d
    @34
    oveq12d
    oveqd
    mpteq12dv
    cnveqd
    funeqd
    ralbidv
    rabeqbidv
    ismon.x
    ismon.y
    @13
    cvv
    wcel
    wph
    @11
    vf
    @12
    cX
    cY
    cH
    ovex
    rabex
    a1i
    ovmpt2d
    eleq2d
    @11
    @18
    vf
    cF
    @12
    @3
    cF
    wceq
    #
    @10
    @17
    vz
    cB
    @35
    @9
    @16
    @35
    @8
    @15
    @35
    vg
    @2
    @7
    @14
    @3
    cF
    @4
    @6
    oveq1
    mpteq2dv
    cnveqd
    funeqd
    ralbidv
    elrab
    syl6bb
end
