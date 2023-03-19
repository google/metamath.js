include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "ccat.mm"
include "iscat.mm"
include "ibi.mm"
include "simpl.mm"
include "ralimi.mm"
include "3syl.mm"
include "id.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "opeq2.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "oveq1.mm"
include "opeq12d.mm"
include "oveq1d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rexeqbidv.mm"
include "rspcv.mm"
include "sylc.mm"

theorem catidex
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
  assert |- ( ph -> E. g e. ( X H X ) A. y e. B ( A. f e. ( y H X ) ( g ( <. y , X >. .x. X ) f ) = f /\ A. f e. ( X H y ) ( f ( <. X , X >. .x. y ) g ) = f ) )

  proof
    wph
    cX
    cB
    wcel
    vg
    cv
    #
    vf
    cv
    #
    vy
    cv
    #
    vx
    cv
    #
    cop
    #
    @3
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
    @3
    cH
    co
    #
    wral
    #
    @1
    @0
    @3
    @3
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
    @3
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
    @3
    @3
    cH
    co
    #
    wrex
    #
    vx
    cB
    wral
    #
    @0
    @1
    @2
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
    #
    catidex.x
    wph
    cC
    ccat
    wcel
    #
    @19
    @0
    @1
    @3
    @2
    cop
    #
    vz
    cv
    #
    c.x
    co
    co
    #
    @3
    @39
    cH
    co
    wcel
    vk
    cv
    #
    @0
    @2
    @39
    cop
    vw
    cv
    #
    c.x
    co
    co
    @1
    @38
    @42
    c.x
    co
    co
    @41
    @40
    @3
    @39
    cop
    @42
    c.x
    co
    co
    wceq
    vk
    @39
    @42
    cH
    co
    wral
    vw
    cB
    wral
    wa
    vg
    @2
    @39
    cH
    co
    wral
    vf
    @14
    wral
    vz
    cB
    wral
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    #
    @20
    catidex.c
    @37
    @45
    vx
    vy
    vz
    vw
    cB
    cC
    c.x
    vf
    vg
    vk
    cH
    ccat
    catidex.b
    catidex.h
    catidex.o
    iscat
    ibi
    @44
    @19
    vx
    cB
    @19
    @43
    simpl
    ralimi
    3syl
    @19
    @36
    vx
    cX
    cB
    @3
    cX
    wceq
    #
    @17
    @34
    vg
    @18
    @35
    @46
    @3
    cX
    @3
    cX
    cH
    @46
    id
    #
    @47
    oveq12d
    @46
    @16
    @33
    vy
    cB
    @46
    @9
    @26
    @15
    @32
    @46
    @7
    @24
    vf
    @8
    @25
    @3
    cX
    @2
    cH
    oveq2
    @46
    @6
    @23
    @1
    @46
    @5
    @22
    @0
    @1
    @46
    @4
    @21
    @3
    cX
    c.x
    @3
    cX
    @2
    opeq2
    @47
    oveq12d
    oveqd
    eqeq1d
    raleqbidv
    @46
    @13
    @30
    vf
    @14
    @31
    @3
    cX
    @2
    cH
    oveq1
    @46
    @12
    @29
    @1
    @46
    @11
    @28
    @1
    @0
    @46
    @10
    @27
    @2
    c.x
    @46
    @3
    cX
    @3
    cX
    @47
    @47
    opeq12d
    oveq1d
    oveqd
    eqeq1d
    raleqbidv
    anbi12d
    ralbidv
    rexeqbidv
    rspcv
    sylc
end
