include "ccrg.mm"
include "wcel.mm"
include "cv.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cgrp.mm"
include "crg.mm"
include "wral.mm"
include "wi.mm"
include "simprl.mm"
include "2ralimi.mm"
include "ralrot3.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "3ad2ant1.mm"
include "ax-mp.mm"
include "rspn0.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "rspc3v.mm"
include "3com12.mm"
include "syl5com.mm"
include "sylbi.mm"
include "eqcom.mm"
include "syl6ibr.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "crngcom.mm"
include "3expb.mm"
include "expcom.mm"
include "ancoms.mm"
include "3adant3.mm"
include "impcom.mm"
include "eqtrd.mm"
include "cvv.mm"
include "cmpt2.mm"
include "a1i.mm"
include "oveq12.mm"
include "simp2.mm"
include "simp3.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "simp1.mm"
include "simpl1.mm"
include "ringgrp.mm"
include "3ad2ant2.mm"
include "ralcom.mm"
include "eleq1d.mm"
include "rspc2v.mm"
include "3syl.mm"
include "3adant1.mm"
include "ringcl.mm"
include "3expib.mm"
include "3eqtr4rd.mm"

theorem rmodislmodlem
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let c.pl: class .+
  let c.pd: class .+^
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let cF: class F
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume rmodislmod.v: |- V = ( Base ` R )
  assume rmodislmod.a: |- .+ = ( +g ` R )
  assume rmodislmod.s: |- .x. = ( .s ` R )
  assume rmodislmod.f: |- F = ( Scalar ` R )
  assume rmodislmod.k: |- K = ( Base ` F )
  assume rmodislmod.p: |- .+^ = ( +g ` F )
  assume rmodislmod.t: |- .X. = ( .r ` F )
  assume rmodislmod.u: |- .1. = ( 1r ` F )
  assume rmodislmod.r: |- ( R e. Grp /\ F e. Ring /\ A. q e. K A. r e. K A. x e. V A. w e. V ( ( ( w .x. r ) e. V /\ ( ( w .+ x ) .x. r ) = ( ( w .x. r ) .+ ( x .x. r ) ) /\ ( w .x. ( q .+^ r ) ) = ( ( w .x. q ) .+ ( w .x. r ) ) ) /\ ( ( w .x. ( q .X. r ) ) = ( ( w .x. q ) .x. r ) /\ ( w .x. .1. ) = w ) ) )
  assume rmodislmod.m: |- .* = ( s e. K , v e. V |-> ( v .x. s ) )
  assume rmodislmod.l: |- L = ( R sSet <. ( .s ` ndx ) , .* >. )

  disjoint .X. q
  disjoint .X. r
  disjoint .X. w
  disjoint .X. x
  disjoint q r
  disjoint q w
  disjoint q x
  disjoint r w
  disjoint r x
  disjoint w x
  disjoint .X. s
  disjoint .X. v
  disjoint s v
  disjoint .x. q
  disjoint .x. r
  disjoint .x. w
  disjoint .x. x
  disjoint .x. s
  disjoint .x. v
  disjoint K q
  disjoint K r
  disjoint K x
  disjoint K s
  disjoint K v
  disjoint V q
  disjoint V r
  disjoint V w
  disjoint V x
  disjoint V s
  disjoint V v
  disjoint a r
  disjoint a w
  disjoint a s
  disjoint a v
  disjoint b q
  disjoint b r
  disjoint b w
  disjoint b s
  disjoint b v
  disjoint c s
  disjoint c v
  disjoint c w
  assert |- ( ( F e. CRing /\ ( a e. K /\ b e. K /\ c e. V ) ) -> ( ( a .X. b ) .* c ) = ( a .* ( b .* c ) ) )

  proof
    cF
    ccrg
    wcel
    #
    va
    cv
    #
    cK
    wcel
    #
    vb
    cv
    #
    cK
    wcel
    #
    vc
    cv
    #
    cV
    wcel
    #
    w3a
    #
    wa
    #
    @5
    @3
    c.x
    co
    #
    @1
    c.x
    co
    #
    @5
    @1
    @3
    c.xp
    co
    #
    c.x
    co
    #
    @1
    @3
    @5
    c.as
    co
    #
    c.as
    co
    #
    @11
    @5
    c.as
    co
    #
    @8
    @10
    @5
    @3
    @1
    c.xp
    co
    #
    c.x
    co
    #
    @12
    @7
    @10
    @17
    wceq
    #
    @0
    cR
    cgrp
    wcel
    #
    cF
    crg
    wcel
    #
    vw
    cv
    #
    vr
    cv
    #
    c.x
    co
    #
    cV
    wcel
    #
    @21
    vx
    cv
    #
    c.pl
    co
    @22
    c.x
    co
    @23
    @25
    @22
    c.x
    co
    c.pl
    co
    wceq
    #
    @21
    vq
    cv
    #
    @22
    c.pd
    co
    c.x
    co
    @21
    @27
    c.x
    co
    #
    @23
    c.pl
    co
    wceq
    #
    w3a
    #
    @21
    @27
    @22
    c.xp
    co
    #
    c.x
    co
    #
    @28
    @22
    c.x
    co
    #
    wceq
    #
    @21
    c.1
    c.x
    co
    @21
    wceq
    #
    wa
    #
    wa
    #
    vw
    cV
    wral
    vx
    cV
    wral
    #
    vr
    cK
    wral
    vq
    cK
    wral
    #
    w3a
    #
    @7
    @18
    wi
    #
    rmodislmod.r
    @39
    @19
    @41
    @20
    @39
    @34
    vw
    cV
    wral
    #
    vx
    cV
    wral
    #
    vr
    cK
    wral
    vq
    cK
    wral
    #
    @41
    @38
    @43
    vq
    vr
    cK
    cK
    @37
    @34
    vx
    vw
    cV
    cV
    @30
    @34
    @35
    simprl
    2ralimi
    2ralimi
    @44
    @7
    @17
    @10
    wceq
    #
    @18
    @44
    @42
    vr
    cK
    wral
    vq
    cK
    wral
    #
    vx
    cV
    wral
    #
    @7
    @45
    wi
    @42
    vq
    vr
    vx
    cK
    cK
    cV
    ralrot3
    @47
    @46
    @7
    @45
    cV
    c0
    wne
    #
    @47
    @46
    wi
    @40
    @48
    rmodislmod.r
    @19
    @20
    @48
    @39
    cV
    cR
    rmodislmod.v
    grpbn0
    3ad2ant1
    ax-mp
    #
    @46
    vx
    cV
    rspn0
    ax-mp
    @4
    @2
    @6
    @46
    @45
    wi
    @34
    @45
    @21
    @3
    @22
    c.xp
    co
    #
    c.x
    co
    #
    @21
    @3
    c.x
    co
    #
    @22
    c.x
    co
    #
    wceq
    @21
    @16
    c.x
    co
    #
    @52
    @1
    c.x
    co
    #
    wceq
    vq
    vr
    vw
    @3
    @1
    @5
    cK
    cK
    cV
    vq
    vb
    weq
    #
    @32
    @51
    @33
    @53
    @56
    @31
    @50
    @21
    c.x
    @27
    @3
    @22
    c.xp
    oveq1
    oveq2d
    @56
    @28
    @52
    @22
    c.x
    @27
    @3
    @21
    c.x
    oveq2
    oveq1d
    eqeq12d
    vr
    va
    weq
    #
    @51
    @54
    @53
    @55
    @57
    @50
    @16
    @21
    c.x
    @22
    @1
    @3
    c.xp
    oveq2
    oveq2d
    @22
    @1
    @52
    c.x
    oveq2
    eqeq12d
    vw
    vc
    weq
    #
    @54
    @17
    @55
    @10
    @21
    @5
    @16
    c.x
    oveq1
    @58
    @52
    @9
    @1
    c.x
    @21
    @5
    @3
    c.x
    oveq1
    #
    oveq1d
    eqeq12d
    rspc3v
    3com12
    syl5com
    sylbi
    @10
    @17
    eqcom
    syl6ibr
    syl
    3ad2ant3
    ax-mp
    adantl
    @8
    @16
    @11
    @5
    c.x
    @7
    @0
    @16
    @11
    wceq
    #
    @2
    @4
    @0
    @60
    wi
    #
    @6
    @4
    @2
    @61
    @0
    @4
    @2
    wa
    @60
    @0
    @4
    @2
    @60
    cK
    cF
    c.xp
    @3
    @1
    rmodislmod.k
    rmodislmod.t
    crngcom
    3expb
    expcom
    ancoms
    3adant3
    impcom
    oveq2d
    eqtrd
    @7
    @14
    @10
    wceq
    @0
    @7
    @14
    @1
    @9
    c.as
    co
    @10
    @7
    @13
    @9
    @1
    c.as
    @7
    vs
    vv
    @3
    @5
    cK
    cV
    vv
    cv
    #
    vs
    cv
    #
    c.x
    co
    #
    @9
    c.as
    cvv
    c.as
    vs
    vv
    cK
    cV
    @64
    cmpt2
    wceq
    @7
    rmodislmod.m
    a1i
    #
    vs
    vb
    weq
    #
    vv
    vc
    weq
    #
    wa
    @64
    @9
    wceq
    #
    @7
    @67
    @66
    @68
    @62
    @5
    @63
    @3
    c.x
    oveq12
    ancoms
    adantl
    @2
    @4
    @6
    simp2
    @2
    @4
    @6
    simp3
    #
    @7
    @5
    @3
    c.x
    ovexd
    ovmpt2d
    oveq2d
    @7
    vs
    vv
    @1
    @9
    cK
    cV
    @64
    @10
    c.as
    cvv
    @65
    vs
    va
    weq
    #
    @62
    @9
    wceq
    #
    wa
    @64
    @10
    wceq
    #
    @7
    @71
    @70
    @72
    @62
    @9
    @63
    @1
    c.x
    oveq12
    ancoms
    adantl
    @2
    @4
    @6
    simp1
    @4
    @6
    @9
    cV
    wcel
    #
    @2
    @40
    @4
    @6
    wa
    #
    @73
    wi
    #
    rmodislmod.r
    @39
    @19
    @75
    @20
    @39
    @24
    vw
    cV
    wral
    #
    vx
    cV
    wral
    #
    vr
    cK
    wral
    #
    vq
    cK
    wral
    #
    @78
    @75
    @38
    @77
    vq
    vr
    cK
    cK
    @37
    @24
    vx
    vw
    cV
    cV
    @24
    @26
    @29
    @36
    simpl1
    2ralimi
    2ralimi
    cK
    c0
    wne
    #
    @79
    @78
    wi
    @40
    @80
    rmodislmod.r
    @20
    @19
    @80
    @39
    @20
    cF
    cgrp
    wcel
    @80
    cF
    ringgrp
    cK
    cF
    rmodislmod.k
    grpbn0
    syl
    3ad2ant2
    ax-mp
    @78
    vq
    cK
    rspn0
    ax-mp
    @78
    @76
    vr
    cK
    wral
    #
    vx
    cV
    wral
    #
    @75
    @76
    vr
    vx
    cK
    cV
    ralcom
    @82
    @81
    @74
    @73
    @48
    @82
    @81
    wi
    @49
    @81
    vx
    cV
    rspn0
    ax-mp
    @24
    @73
    @52
    cV
    wcel
    vr
    vw
    @3
    @5
    cK
    cV
    vr
    vb
    weq
    @23
    @52
    cV
    @22
    @3
    @21
    c.x
    oveq2
    eleq1d
    @58
    @52
    @9
    cV
    @59
    eleq1d
    rspc2v
    syl5com
    sylbi
    3syl
    3ad2ant3
    ax-mp
    3adant1
    @7
    @9
    @1
    c.x
    ovexd
    ovmpt2d
    eqtrd
    adantl
    @7
    @15
    @12
    wceq
    @0
    @7
    vs
    vv
    @11
    @5
    cK
    cV
    @64
    @12
    c.as
    cvv
    @65
    @63
    @11
    wceq
    #
    @67
    wa
    @64
    @12
    wceq
    #
    @7
    @67
    @83
    @84
    @62
    @5
    @63
    @11
    c.x
    oveq12
    ancoms
    adantl
    @2
    @4
    @11
    cK
    wcel
    #
    @6
    @40
    @2
    @4
    wa
    @85
    wi
    #
    rmodislmod.r
    @20
    @19
    @86
    @39
    @20
    @2
    @4
    @85
    cK
    cF
    c.xp
    @1
    @3
    rmodislmod.k
    rmodislmod.t
    ringcl
    3expib
    3ad2ant2
    ax-mp
    3adant3
    @69
    @7
    @5
    @11
    c.x
    ovexd
    ovmpt2d
    adantl
    3eqtr4rd
end
