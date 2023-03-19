include "ccat.mm"
include "wcel.mm"
include "cdm.mm"
include "wceq.mm"
include "csubc.mm"
include "cfv.mm"
include "cssc.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "cop.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "chomf.mm"
include "ccid.mm"
include "cco.mm"
include "wsbc.mm"
include "cab.mm"
include "csb.mm"
include "cvv.mm"
include "simpl.mm"
include "sscpwex.mm"
include "ss2abi.mm"
include "ssexi.mm"
include "csbex.mm"
include "a1i.mm"
include "df-subc.mm"
include "fvmpts.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "sbcel2.mm"
include "wi.mm"
include "elex.mm"
include "sscrel.mm"
include "brrelexi.mm"
include "adantr.mm"
include "df-sbc.mm"
include "simpr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "breq12d.mm"
include "vex.mm"
include "dmex.mm"
include "dmeqd.mm"
include "simpllr.mm"
include "eqtr4d.mm"
include "fveq1d.mm"
include "simplr.mm"
include "oveqd.mm"
include "eleq12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "sbcied2.mm"
include "adantlr.mm"
include "sbcied.mm"
include "syl5bbr.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "3bitr2d.mm"

theorem issubc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cJ: class J
  let vc: setvar c
  let vj: setvar j
  let vs: setvar s
  assume issubc.h: |- H = ( Homf ` C )
  assume issubc.i: |- .1. = ( Id ` C )
  assume issubc.o: |- .x. = ( comp ` C )
  assume issubc.c: |- ( ph -> C e. Cat )
  assume issubc.s: |- ( ph -> S = dom dom J )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint C f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint C g
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint S f
  disjoint S g
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c s
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint C c
  disjoint f j
  disjoint f s
  disjoint g j
  disjoint g s
  disjoint j s
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint C j
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint J c
  disjoint J j
  disjoint J s
  disjoint S c
  disjoint S j
  disjoint S s
  disjoint .1. c
  disjoint .1. j
  disjoint .1. s
  disjoint H c
  disjoint H j
  disjoint .x. c
  disjoint .x. j
  disjoint .x. s
  assert |- ( ph -> ( J e. ( Subcat ` C ) <-> ( J C_cat H /\ A. x e. S ( ( .1. ` x ) e. ( x J x ) /\ A. y e. S A. z e. S A. f e. ( x J y ) A. g e. ( y J z ) ( g ( <. x , y >. .x. z ) f ) e. ( x J z ) ) ) ) )

  proof
    wph
    cC
    ccat
    wcel
    #
    cS
    cJ
    cdm
    #
    cdm
    #
    wceq
    #
    cJ
    cC
    csubc
    cfv
    #
    wcel
    #
    cJ
    cH
    cssc
    wbr
    #
    vx
    cv
    #
    c.1
    cfv
    #
    @7
    @7
    cJ
    co
    #
    wcel
    #
    vg
    cv
    #
    vf
    cv
    #
    @7
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    c.x
    co
    #
    co
    #
    @7
    @15
    cJ
    co
    #
    wcel
    #
    vg
    @13
    @15
    cJ
    co
    #
    wral
    #
    vf
    @7
    @13
    cJ
    co
    #
    wral
    #
    vz
    cS
    wral
    #
    vy
    cS
    wral
    #
    wa
    #
    vx
    cS
    wral
    #
    wa
    #
    wb
    issubc.c
    issubc.s
    @0
    @3
    wa
    #
    @5
    cJ
    vc
    cC
    vj
    cv
    #
    vc
    cv
    #
    chomf
    cfv
    #
    cssc
    wbr
    #
    @7
    @31
    ccid
    cfv
    #
    cfv
    #
    @7
    @7
    @30
    co
    #
    wcel
    #
    @11
    @12
    @14
    @15
    @31
    cco
    cfv
    #
    co
    #
    co
    #
    @7
    @15
    @30
    co
    #
    wcel
    #
    vg
    @13
    @15
    @30
    co
    #
    wral
    #
    vf
    @7
    @13
    @30
    co
    #
    wral
    #
    vz
    vs
    cv
    #
    wral
    #
    vy
    @47
    wral
    #
    wa
    #
    vx
    @47
    wral
    #
    vs
    @30
    cdm
    #
    cdm
    #
    wsbc
    #
    wa
    #
    vj
    cab
    #
    csb
    #
    wcel
    #
    cJ
    @56
    wcel
    #
    vc
    cC
    wsbc
    #
    @28
    @29
    @4
    @57
    cJ
    @29
    @0
    @57
    cvv
    wcel
    #
    @4
    @57
    wceq
    @0
    @3
    simpl
    #
    @61
    @29
    vc
    cC
    @56
    @56
    @33
    vj
    cab
    vj
    @32
    sscpwex
    @55
    @33
    vj
    @33
    @54
    simpl
    ss2abi
    ssexi
    csbex
    a1i
    vc
    cC
    @56
    ccat
    csubc
    cvv
    vx
    vy
    vz
    vf
    vg
    vj
    vs
    vc
    df-subc
    fvmpts
    syl2anc
    eleq2d
    @60
    @58
    wb
    @29
    vc
    cC
    cJ
    @56
    sbcel2
    a1i
    @29
    @59
    @28
    vc
    cC
    ccat
    @62
    @29
    @31
    cC
    wceq
    #
    wa
    #
    cJ
    cvv
    wcel
    #
    @59
    @28
    @59
    @65
    wi
    @64
    cJ
    @56
    elex
    a1i
    @28
    @65
    wi
    @64
    @6
    @65
    @27
    cJ
    cH
    cssc
    sscrel
    brrelexi
    adantr
    a1i
    @64
    @65
    @59
    @28
    wb
    @59
    @55
    vj
    cJ
    wsbc
    @64
    @65
    wa
    #
    @28
    @55
    vj
    cJ
    df-sbc
    @66
    @55
    @28
    vj
    cJ
    cvv
    @64
    @65
    simpr
    @64
    @30
    cJ
    wceq
    #
    @55
    @28
    wb
    @65
    @64
    @67
    wa
    #
    @33
    @6
    @54
    @27
    @68
    @30
    cJ
    @32
    cH
    cssc
    @64
    @67
    simpr
    #
    @64
    @32
    cH
    wceq
    @67
    @64
    @32
    cC
    chomf
    cfv
    cH
    @64
    @31
    cC
    chomf
    @29
    @63
    simpr
    fveq2d
    issubc.h
    syl6eqr
    adantr
    breq12d
    @68
    @51
    @27
    vs
    @53
    cS
    cvv
    @53
    cvv
    wcel
    @68
    @52
    @30
    vj
    vex
    dmex
    dmex
    a1i
    @68
    @53
    @2
    cS
    @68
    @52
    @1
    @68
    @30
    cJ
    @69
    dmeqd
    dmeqd
    @0
    @3
    @63
    @67
    simpllr
    eqtr4d
    @68
    @47
    cS
    wceq
    #
    wa
    #
    @50
    @26
    vx
    @47
    cS
    @68
    @70
    simpr
    #
    @71
    @37
    @10
    @49
    @25
    @71
    @35
    @8
    @36
    @9
    @71
    @7
    @34
    c.1
    @71
    @34
    cC
    ccid
    cfv
    c.1
    @71
    @31
    cC
    ccid
    @29
    @63
    @67
    @70
    simpllr
    #
    fveq2d
    issubc.i
    syl6eqr
    fveq1d
    @71
    @30
    cJ
    @7
    @7
    @64
    @67
    @70
    simplr
    #
    oveqd
    eleq12d
    @71
    @48
    @24
    vy
    @47
    cS
    @72
    @71
    @46
    @23
    vz
    @47
    cS
    @72
    @71
    @44
    @21
    vf
    @45
    @22
    @71
    @30
    cJ
    @7
    @13
    @74
    oveqd
    @71
    @42
    @19
    vg
    @43
    @20
    @71
    @30
    cJ
    @13
    @15
    @74
    oveqd
    @71
    @40
    @17
    @41
    @18
    @71
    @39
    @16
    @11
    @12
    @71
    @38
    c.x
    @14
    @15
    @71
    @38
    cC
    cco
    cfv
    c.x
    @71
    @31
    cC
    cco
    @73
    fveq2d
    issubc.o
    syl6eqr
    oveqd
    oveqd
    @71
    @30
    cJ
    @7
    @15
    @74
    oveqd
    eleq12d
    raleqbidv
    raleqbidv
    raleqbidv
    raleqbidv
    anbi12d
    raleqbidv
    sbcied2
    anbi12d
    adantlr
    sbcied
    syl5bbr
    ex
    pm5.21ndd
    sbcied
    3bitr2d
    syl2anc
end
