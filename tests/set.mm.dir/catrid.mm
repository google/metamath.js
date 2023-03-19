include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "wa.mm"
include "wi.mm"
include "simpr.mm"
include "ralimi.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "crio.mm"
include "cidval.mm"
include "wreu.mm"
include "catideu.mm"
include "riotacl2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "sseldi.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "oveqd.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "oveq1.mm"
include "id.mm"
include "eqeq12d.mm"

theorem catrid
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume catidcl.b: |- B = ( Base ` C )
  assume catidcl.h: |- H = ( Hom ` C )
  assume catidcl.i: |- .1. = ( Id ` C )
  assume catidcl.c: |- ( ph -> C e. Cat )
  assume catidcl.x: |- ( ph -> X e. B )
  assume catlid.o: |- .x. = ( comp ` C )
  assume catlid.y: |- ( ph -> Y e. B )
  assume catlid.f: |- ( ph -> F e. ( X H Y ) )


  assert |- ( ph -> ( F ( <. X , X >. .x. Y ) ( .1. ` X ) ) = F )

  proof
    wph
    cF
    cX
    cY
    cH
    co
    #
    wcel
    vf
    cv
    #
    cX
    c.1
    cfv
    #
    cX
    cX
    cop
    #
    cY
    c.x
    co
    #
    co
    #
    @1
    wceq
    #
    vf
    @0
    wral
    #
    cF
    @2
    @4
    co
    #
    cF
    wceq
    #
    catlid.f
    wph
    cY
    cB
    wcel
    @1
    @2
    @3
    vy
    cv
    #
    c.x
    co
    #
    co
    #
    @1
    wceq
    #
    vf
    cX
    @10
    cH
    co
    #
    wral
    #
    vy
    cB
    wral
    #
    @7
    catlid.y
    wph
    @2
    @1
    vg
    cv
    #
    @11
    co
    #
    @1
    wceq
    #
    vf
    @14
    wral
    #
    vy
    cB
    wral
    #
    vg
    cX
    cX
    cH
    co
    #
    crab
    #
    wcel
    #
    @16
    wph
    @17
    @1
    @10
    cX
    cop
    cX
    c.x
    co
    co
    @1
    wceq
    vf
    @10
    cX
    cH
    co
    wral
    #
    @20
    wa
    #
    vy
    cB
    wral
    #
    vg
    @22
    crab
    #
    @23
    @2
    @27
    @21
    vg
    @22
    @27
    @21
    wi
    @17
    @22
    wcel
    @26
    @20
    vy
    cB
    @25
    @20
    simpr
    ralimi
    a1i
    ss2rabi
    wph
    @2
    @27
    vg
    @22
    crio
    #
    @28
    wph
    vy
    cB
    cC
    c.x
    c.1
    vf
    vg
    cH
    cX
    catidcl.b
    catidcl.h
    catlid.o
    catidcl.c
    catidcl.i
    catidcl.x
    cidval
    wph
    @27
    vg
    @22
    wreu
    @29
    @28
    wcel
    wph
    vy
    cB
    cC
    c.x
    vf
    vg
    cH
    cX
    catidcl.b
    catidcl.h
    catlid.o
    catidcl.c
    catidcl.x
    catideu
    @27
    vg
    @22
    riotacl2
    syl
    eqeltrd
    sseldi
    @24
    @2
    @22
    wcel
    @16
    @21
    @16
    vg
    @2
    @22
    @17
    @2
    wceq
    #
    @19
    @13
    vy
    vf
    cB
    @14
    @30
    @18
    @12
    @1
    @17
    @2
    @1
    @11
    oveq2
    eqeq1d
    2ralbidv
    elrab
    simprbi
    syl
    @15
    @7
    vy
    cY
    cB
    @10
    cY
    wceq
    #
    @13
    @6
    vf
    @14
    @0
    @10
    cY
    cX
    cH
    oveq2
    @31
    @12
    @5
    @1
    @31
    @11
    @4
    @1
    @2
    @10
    cY
    @3
    c.x
    oveq2
    oveqd
    eqeq1d
    raleqbidv
    rspcv
    sylc
    @6
    @9
    vf
    cF
    @0
    @1
    cF
    wceq
    #
    @5
    @8
    @1
    cF
    @1
    cF
    @2
    @4
    oveq1
    @32
    id
    eqeq12d
    rspcv
    sylc
end
