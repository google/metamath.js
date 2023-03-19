include "cv.mm"
include "cop.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "catidex.mm"
include "wi.mm"
include "wcel.mm"
include "oveq1.mm"
include "opeq1.mm"
include "oveq1d.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "ralrimivw.mm"
include "weq.mm"
include "an3.mm"
include "id.mm"
include "eqeq12d.mm"
include "im2anan9r.mm"
include "eqtr2.mm"
include "equcomd.mm"
include "syl56.mm"
include "rgen2a.mm"
include "a1i.mm"
include "ralbidv.mm"
include "rmo4.mm"
include "sylibr.mm"
include "rmoim.mm"
include "sylc.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem catideu
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cX: class X
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let vh: setvar h
  assume catidex.b: |- B = ( Base ` C )
  assume catidex.h: |- H = ( Hom ` C )
  assume catidex.o: |- .x. = ( comp ` C )
  assume catidex.c: |- ( ph -> C e. Cat )
  assume catidex.x: |- ( ph -> X e. B )

  disjoint f g
  disjoint f y
  disjoint B f
  disjoint g y
  disjoint B g
  disjoint B y
  disjoint C f
  disjoint C g
  disjoint C y
  disjoint g ph
  disjoint X f
  disjoint X g
  disjoint X y
  disjoint H f
  disjoint H g
  disjoint H y
  disjoint .x. f
  disjoint .x. g
  disjoint .x. y
  disjoint f k
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint g k
  disjoint g w
  disjoint g x
  disjoint g z
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B z
  disjoint C k
  disjoint C w
  disjoint C x
  disjoint C z
  disjoint f h
  disjoint g h
  disjoint h x
  disjoint h y
  disjoint X h
  disjoint X x
  disjoint h k
  disjoint h w
  disjoint h z
  disjoint H h
  disjoint H k
  disjoint H w
  disjoint H x
  disjoint H z
  disjoint .x. h
  disjoint .x. k
  disjoint .x. w
  disjoint .x. x
  disjoint .x. z
  assert |- ( ph -> E! g e. ( X H X ) A. y e. B ( A. f e. ( y H X ) ( g ( <. y , X >. .x. X ) f ) = f /\ A. f e. ( X H y ) ( f ( <. X , X >. .x. y ) g ) = f ) )

  proof
    wph
    vg
    cv
    #
    vf
    cv
    #
    vy
    cv
    #
    cX
    cop
    #
    cX
    c.x
    co
    #
    co
    #
    @1
    wceq
    #
    vf
    @2
    cX
    cH
    co
    #
    wral
    #
    @1
    @0
    cX
    cX
    cop
    #
    @2
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
    @2
    cH
    co
    #
    wral
    #
    wa
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
    wrex
    @16
    vg
    @17
    wrmo
    #
    @16
    vg
    @17
    wreu
    wph
    vy
    cB
    cC
    c.x
    vf
    vg
    cH
    cX
    catidex.b
    catidex.h
    catidex.o
    catidex.c
    catidex.x
    catidex
    wph
    @16
    @0
    @1
    @9
    cX
    c.x
    co
    #
    co
    #
    @1
    wceq
    #
    vf
    @17
    wral
    #
    @1
    @0
    @19
    co
    #
    @1
    wceq
    #
    vf
    @17
    wral
    #
    wa
    #
    wi
    #
    vg
    @17
    wral
    @26
    vg
    @17
    wrmo
    #
    @18
    wph
    @27
    vg
    @17
    wph
    cX
    cB
    wcel
    @27
    catidex.x
    @15
    @26
    vy
    cX
    cB
    @2
    cX
    wceq
    #
    @8
    @22
    @14
    @25
    @29
    @6
    @21
    vf
    @7
    @17
    @2
    cX
    cX
    cH
    oveq1
    @29
    @5
    @20
    @1
    @29
    @4
    @19
    @0
    @1
    @29
    @3
    @9
    cX
    c.x
    @2
    cX
    cX
    opeq1
    oveq1d
    oveqd
    eqeq1d
    raleqbidv
    @29
    @12
    @24
    vf
    @13
    @17
    @2
    cX
    cX
    cH
    oveq2
    @29
    @11
    @23
    @1
    @29
    @10
    @19
    @1
    @0
    @2
    cX
    @9
    c.x
    oveq2
    oveqd
    eqeq1d
    raleqbidv
    anbi12d
    rspcv
    syl
    ralrimivw
    wph
    @26
    vh
    cv
    #
    @1
    @19
    co
    #
    @1
    wceq
    #
    vf
    @17
    wral
    #
    @1
    @30
    @19
    co
    #
    @1
    wceq
    #
    vf
    @17
    wral
    #
    wa
    #
    wa
    #
    vg
    vh
    weq
    #
    wi
    #
    vh
    @17
    wral
    vg
    @17
    wral
    #
    @28
    @41
    wph
    @40
    vg
    vh
    @17
    @38
    @22
    @36
    wa
    @0
    @17
    wcel
    #
    @30
    @17
    wcel
    #
    wa
    @0
    @30
    @19
    co
    #
    @30
    wceq
    #
    @44
    @0
    wceq
    #
    wa
    #
    @39
    @22
    @25
    @33
    @36
    an3
    @43
    @22
    @45
    @42
    @36
    @46
    @21
    @45
    vf
    @30
    @17
    vf
    vh
    weq
    #
    @20
    @44
    @1
    @30
    @1
    @30
    @0
    @19
    oveq2
    @48
    id
    eqeq12d
    rspcv
    @35
    @46
    vf
    @0
    @17
    vf
    vg
    weq
    #
    @34
    @44
    @1
    @0
    @1
    @0
    @30
    @19
    oveq1
    @49
    id
    eqeq12d
    rspcv
    im2anan9r
    @47
    vh
    vg
    @44
    @30
    @0
    eqtr2
    equcomd
    syl56
    rgen2a
    a1i
    @26
    @37
    vg
    vh
    @17
    @39
    @22
    @33
    @25
    @36
    @39
    @21
    @32
    vf
    @17
    @39
    @20
    @31
    @1
    @0
    @30
    @1
    @19
    oveq1
    eqeq1d
    ralbidv
    @39
    @24
    @35
    vf
    @17
    @39
    @23
    @34
    @1
    @0
    @30
    @1
    @19
    oveq2
    eqeq1d
    ralbidv
    anbi12d
    rmo4
    sylibr
    @16
    @26
    vg
    @17
    rmoim
    sylc
    @16
    vg
    @17
    reu5
    sylanbrc
end
