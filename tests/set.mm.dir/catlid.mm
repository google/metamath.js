include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "wa.mm"
include "wi.mm"
include "simpl.mm"
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
include "oveq1.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "opeq1.mm"
include "oveq1d.mm"
include "oveqd.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"

theorem catlid
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


  assert |- ( ph -> ( ( .1. ` Y ) ( <. X , Y >. .x. Y ) F ) = F )

  proof
    wph
    cF
    cX
    cY
    cH
    co
    #
    wcel
    cY
    c.1
    cfv
    #
    vf
    cv
    #
    cX
    cY
    cop
    #
    cY
    c.x
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @0
    wral
    #
    @1
    cF
    @4
    co
    #
    cF
    wceq
    #
    catlid.f
    wph
    cX
    cB
    wcel
    @1
    @2
    vx
    cv
    #
    cY
    cop
    #
    cY
    c.x
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @10
    cY
    cH
    co
    #
    wral
    #
    vx
    cB
    wral
    #
    @7
    catidcl.x
    wph
    @1
    vg
    cv
    #
    @2
    @12
    co
    #
    @2
    wceq
    #
    vf
    @15
    wral
    #
    vx
    cB
    wral
    #
    vg
    cY
    cY
    cH
    co
    #
    crab
    #
    wcel
    #
    @17
    wph
    @21
    @2
    @18
    cY
    cY
    cop
    @10
    c.x
    co
    co
    @2
    wceq
    vf
    cY
    @10
    cH
    co
    wral
    #
    wa
    #
    vx
    cB
    wral
    #
    vg
    @23
    crab
    #
    @24
    @1
    @28
    @22
    vg
    @23
    @28
    @22
    wi
    @18
    @23
    wcel
    @27
    @21
    vx
    cB
    @21
    @26
    simpl
    ralimi
    a1i
    ss2rabi
    wph
    @1
    @28
    vg
    @23
    crio
    #
    @29
    wph
    vx
    cB
    cC
    c.x
    c.1
    vf
    vg
    cH
    cY
    catidcl.b
    catidcl.h
    catlid.o
    catidcl.c
    catidcl.i
    catlid.y
    cidval
    wph
    @28
    vg
    @23
    wreu
    @30
    @29
    wcel
    wph
    vx
    cB
    cC
    c.x
    vf
    vg
    cH
    cY
    catidcl.b
    catidcl.h
    catlid.o
    catidcl.c
    catlid.y
    catideu
    @28
    vg
    @23
    riotacl2
    syl
    eqeltrd
    sseldi
    @25
    @1
    @23
    wcel
    @17
    @22
    @17
    vg
    @1
    @23
    @18
    @1
    wceq
    #
    @20
    @14
    vx
    vf
    cB
    @15
    @31
    @19
    @13
    @2
    @18
    @1
    @2
    @12
    oveq1
    eqeq1d
    2ralbidv
    elrab
    simprbi
    syl
    @16
    @7
    vx
    cX
    cB
    @10
    cX
    wceq
    #
    @14
    @6
    vf
    @15
    @0
    @10
    cX
    cY
    cH
    oveq1
    @32
    @13
    @5
    @2
    @32
    @12
    @4
    @1
    @2
    @32
    @11
    @3
    cY
    c.x
    @10
    cX
    cY
    opeq1
    oveq1d
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
    @2
    cF
    wceq
    #
    @5
    @8
    @2
    cF
    @2
    cF
    @1
    @4
    oveq2
    @33
    id
    eqeq12d
    rspcv
    sylc
end
