include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "co.mm"
include "wceq.mm"
include "chom.mm"
include "wral.mm"
include "wa.mm"
include "crio.mm"
include "cmpt.mm"
include "ccid.mm"
include "wcel.mm"
include "w3a.mm"
include "ex.mm"
include "eleq2d.mm"
include "oveqd.mm"
include "3anbi123d.mm"
include "eqeq1d.mm"
include "3imtr3d.mm"
include "3expd.mm"
include "imp41.mm"
include "ralrimiva.mm"
include "jca.mm"
include "wreu.mm"
include "wb.mm"
include "imp.mm"
include "eqid.mm"
include "ccat.mm"
include "adantr.mm"
include "simpr.mm"
include "catideu.mm"
include "oveq1.mm"
include "ralbidv.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "mpteq2dva.mm"
include "cidfval.mm"
include "mpteq1d.mm"
include "3eqtr4d.mm"

theorem catidd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let c.1: class .1.
  let vf: setvar f
  let cH: class H
  let vg: setvar g
  assume catidd.b: |- ( ph -> B = ( Base ` C ) )
  assume catidd.h: |- ( ph -> H = ( Hom ` C ) )
  assume catidd.o: |- ( ph -> .x. = ( comp ` C ) )
  assume catidd.c: |- ( ph -> C e. Cat )
  assume catidd.1: |- ( ( ph /\ x e. B ) -> .1. e. ( x H x ) )
  assume catidd.2: |- ( ( ph /\ ( x e. B /\ y e. B /\ f e. ( y H x ) ) ) -> ( .1. ( <. y , x >. .x. x ) f ) = f )
  assume catidd.3: |- ( ( ph /\ ( x e. B /\ y e. B /\ f e. ( x H y ) ) ) -> ( f ( <. x , x >. .x. y ) .1. ) = f )

  disjoint f y
  disjoint .1. f
  disjoint .1. y
  disjoint B x
  disjoint f x
  disjoint C f
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint f ph
  disjoint ph x
  disjoint ph y
  disjoint f g
  disjoint g y
  disjoint .1. g
  disjoint g x
  disjoint C g
  disjoint g ph
  assert |- ( ph -> ( Id ` C ) = ( x e. B |-> .1. ) )

  proof
    wph
    vx
    cC
    cbs
    cfv
    #
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
    @4
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @3
    @4
    cC
    chom
    cfv
    #
    co
    #
    wral
    #
    @2
    @1
    @4
    @4
    cop
    #
    @3
    @6
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @4
    @3
    @10
    co
    #
    wral
    #
    wa
    #
    vy
    @0
    wral
    #
    vg
    @4
    @4
    @10
    co
    #
    crio
    #
    cmpt
    vx
    @0
    c.1
    cmpt
    cC
    ccid
    cfv
    #
    vx
    cB
    c.1
    cmpt
    wph
    vx
    @0
    @22
    c.1
    wph
    @4
    @0
    wcel
    #
    wa
    #
    c.1
    @2
    @7
    co
    #
    @2
    wceq
    #
    vf
    @11
    wral
    #
    @2
    c.1
    @14
    co
    #
    @2
    wceq
    #
    vf
    @17
    wral
    #
    wa
    #
    vy
    @0
    wral
    #
    @22
    c.1
    wceq
    #
    @25
    @32
    vy
    @0
    @25
    @3
    @0
    wcel
    #
    wa
    #
    @28
    @31
    @36
    @27
    vf
    @11
    wph
    @24
    @35
    @2
    @11
    wcel
    #
    @27
    wph
    @24
    @35
    @37
    @27
    wph
    @4
    cB
    wcel
    #
    @3
    cB
    wcel
    #
    @2
    @3
    @4
    cH
    co
    #
    wcel
    #
    w3a
    #
    c.1
    @2
    @5
    @4
    c.x
    co
    #
    co
    #
    @2
    wceq
    #
    @24
    @35
    @37
    w3a
    @27
    wph
    @42
    @45
    catidd.2
    ex
    wph
    @38
    @24
    @39
    @35
    @41
    @37
    wph
    cB
    @0
    @4
    catidd.b
    eleq2d
    #
    wph
    cB
    @0
    @3
    catidd.b
    eleq2d
    #
    wph
    @40
    @11
    @2
    wph
    cH
    @10
    @3
    @4
    catidd.h
    oveqd
    eleq2d
    3anbi123d
    wph
    @44
    @26
    @2
    wph
    @43
    @7
    c.1
    @2
    wph
    c.x
    @6
    @5
    @4
    catidd.o
    oveqd
    oveqd
    eqeq1d
    3imtr3d
    3expd
    imp41
    ralrimiva
    @36
    @30
    vf
    @17
    wph
    @24
    @35
    @2
    @17
    wcel
    #
    @30
    wph
    @24
    @35
    @48
    @30
    wph
    @38
    @39
    @2
    @4
    @3
    cH
    co
    #
    wcel
    #
    w3a
    #
    @2
    c.1
    @13
    @3
    c.x
    co
    #
    co
    #
    @2
    wceq
    #
    @24
    @35
    @48
    w3a
    @30
    wph
    @51
    @54
    catidd.3
    ex
    wph
    @38
    @24
    @39
    @35
    @50
    @48
    @46
    @47
    wph
    @49
    @17
    @2
    wph
    cH
    @10
    @4
    @3
    catidd.h
    oveqd
    eleq2d
    3anbi123d
    wph
    @53
    @29
    @2
    wph
    @52
    @14
    @2
    c.1
    wph
    c.x
    @6
    @13
    @3
    catidd.o
    oveqd
    oveqd
    eqeq1d
    3imtr3d
    3expd
    imp41
    ralrimiva
    jca
    ralrimiva
    @25
    c.1
    @21
    wcel
    #
    @20
    vg
    @21
    wreu
    @33
    @34
    wb
    wph
    @24
    @55
    wph
    @38
    c.1
    @4
    @4
    cH
    co
    #
    wcel
    #
    @24
    @55
    wph
    @38
    @57
    catidd.1
    ex
    @46
    wph
    @56
    @21
    c.1
    wph
    cH
    @10
    @4
    @4
    catidd.h
    oveqd
    eleq2d
    3imtr3d
    imp
    @25
    vy
    @0
    cC
    @6
    vf
    vg
    @10
    @4
    @0
    eqid
    #
    @10
    eqid
    #
    @6
    eqid
    #
    wph
    cC
    ccat
    wcel
    @24
    catidd.c
    adantr
    wph
    @24
    simpr
    catideu
    @20
    @33
    vg
    @21
    c.1
    @1
    c.1
    wceq
    #
    @19
    @32
    vy
    @0
    @61
    @12
    @28
    @18
    @31
    @61
    @9
    @27
    vf
    @11
    @61
    @8
    @26
    @2
    @1
    c.1
    @2
    @7
    oveq1
    eqeq1d
    ralbidv
    @61
    @16
    @30
    vf
    @17
    @61
    @15
    @29
    @2
    @1
    c.1
    @2
    @14
    oveq2
    eqeq1d
    ralbidv
    anbi12d
    ralbidv
    riota2
    syl2anc
    mpbid
    mpteq2dva
    wph
    vx
    vy
    @0
    cC
    @6
    @23
    vf
    vg
    @10
    @58
    @59
    @60
    catidd.c
    @23
    eqid
    cidfval
    wph
    vx
    cB
    @0
    c.1
    catidd.b
    mpteq1d
    3eqtr4d
end
