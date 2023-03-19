include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "chash.mm"
include "cbs.mm"
include "wne.mm"
include "c0g.mm"
include "wi.mm"
include "simpll.mm"
include "simplr.mm"
include "weq.mm"
include "cif.mm"
include "wrex.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "rexbidv.mm"
include "elrab.mm"
include "ifnefalse.mm"
include "eqeq2d.mm"
include "biimpcd.mm"
include "a1i.mm"
include "ralimdva.mm"
include "ex.mm"
include "com23.mm"
include "rexlimdva.mm"
include "imp.mm"
include "sylbi.mm"
include "impcom.mm"
include "eqid.mm"
include "chpdmat.mm"
include "syl31anc.mm"
include "id.mm"
include "oveq12d.mm"
include "rspccv.mm"
include "3ad2ant3.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "cmnd.mm"
include "ccmn.mm"
include "ply1crng.mm"
include "crngmgp.mm"
include "cmnmnd.mm"
include "3syl.mm"
include "ad2antlr.mm"
include "cgrp.mm"
include "crg.mm"
include "crngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "ringgrp.mm"
include "vr1cl.mm"
include "simpr.mm"
include "csca.mm"
include "ad2antll.mm"
include "adantr.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "asclf.mm"
include "matecl.mm"
include "syl3anc.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "fveq2.mm"
include "eqcoms.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "wb.mm"
include "imbi1d.mm"
include "mpbird.mm"
include "rspcimdv.mm"
include "com24.mm"
include "3imp.mm"
include "grpsubcl.mm"
include "mgpbas.mm"
include "syl6eleq.mm"
include "gsumconst.mm"
include "3eqtrd.mm"

theorem chpscmat
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let c.ex: class .^
  let cG: class G
  let cI: class I
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let vc: setvar c
  let vk: setvar k
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume chp0mat.c: |- C = ( N CharPlyMat R )
  assume chp0mat.p: |- P = ( Poly1 ` R )
  assume chp0mat.a: |- A = ( N Mat R )
  assume chp0mat.x: |- X = ( var1 ` R )
  assume chp0mat.g: |- G = ( mulGrp ` P )
  assume chp0mat.m: |- .^ = ( .g ` G )
  assume chpscmat.d: |- D = { m e. ( Base ` A ) | E. c e. ( Base ` R ) A. i e. N A. j e. N ( i m j ) = if ( i = j , c , ( 0g ` R ) ) }
  assume chpscmat.s: |- S = ( algSc ` P )
  assume chpscmat.m: |- .- = ( -g ` P )

  disjoint A c
  disjoint A m
  disjoint c m
  disjoint D n
  disjoint E n
  disjoint I n
  disjoint M c
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint c i
  disjoint c j
  disjoint c n
  disjoint i j
  disjoint i m
  disjoint i n
  disjoint j m
  disjoint j n
  disjoint m n
  disjoint N c
  disjoint N m
  disjoint N n
  disjoint P n
  disjoint R c
  disjoint R m
  disjoint R n
  disjoint S n
  disjoint i j
  disjoint A i
  disjoint A j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint X i
  disjoint X j
  disjoint D k
  disjoint k n
  disjoint E k
  disjoint I k
  disjoint M k
  disjoint c k
  disjoint i k
  disjoint j k
  disjoint k m
  disjoint S k
  disjoint .- k
  disjoint .0. i
  disjoint .0. j
  disjoint .0. k
  disjoint i k
  disjoint j k
  disjoint A k
  disjoint G k
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint P k
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint X k
  assert |- ( ( ( N e. Fin /\ R e. CRing ) /\ ( M e. D /\ I e. N /\ A. n e. N ( n M n ) = E ) ) -> ( C ` M ) = ( ( # ` N ) .^ ( X .- ( S ` E ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cM
    cD
    wcel
    #
    cI
    cN
    wcel
    #
    vn
    cv
    #
    @5
    cM
    co
    #
    cE
    wceq
    #
    vn
    cN
    wral
    #
    w3a
    #
    wa
    #
    cM
    cC
    cfv
    #
    cG
    vk
    cN
    cX
    vk
    cv
    #
    @12
    cM
    co
    #
    cS
    cfv
    #
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cG
    vk
    cN
    cX
    cE
    cS
    cfv
    #
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cN
    chash
    cfv
    @19
    c.ex
    co
    #
    @10
    @0
    @1
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @25
    @26
    cM
    co
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    @11
    @17
    wceq
    @0
    @1
    @9
    simpll
    #
    @0
    @1
    @9
    simplr
    @9
    @24
    @2
    @3
    @4
    @24
    @8
    @24
    cM
    @25
    @26
    vm
    cv
    #
    co
    #
    vi
    vj
    weq
    vc
    cv
    #
    @29
    cif
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    vc
    cR
    cbs
    cfv
    #
    wrex
    #
    vm
    @23
    crab
    #
    cD
    @42
    vm
    cM
    @23
    elrabi
    chpscmat.d
    eleq2s
    #
    3ad2ant1
    adantl
    @9
    @2
    @33
    @3
    @4
    @2
    @33
    wi
    #
    @8
    @45
    cM
    @43
    cD
    cM
    @43
    wcel
    @24
    @28
    @38
    wceq
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    vc
    @41
    wrex
    #
    wa
    @45
    @42
    @49
    vm
    cM
    @23
    @35
    cM
    wceq
    #
    @40
    @48
    vc
    @41
    @50
    @39
    @46
    vi
    vj
    cN
    cN
    @50
    @36
    @28
    @38
    @25
    @26
    @35
    cM
    oveq
    eqeq1d
    2ralbidv
    rexbidv
    elrab
    @24
    @49
    @45
    @24
    @48
    @45
    vc
    @41
    @24
    @37
    @41
    wcel
    wa
    #
    @2
    @48
    @33
    @51
    @2
    @48
    @33
    wi
    @51
    @2
    wa
    #
    @47
    @32
    vi
    cN
    @52
    @25
    cN
    wcel
    wa
    #
    @46
    @31
    vj
    cN
    @46
    @31
    wi
    @53
    @26
    cN
    wcel
    wa
    @27
    @46
    @30
    @27
    @38
    @29
    @28
    @25
    @26
    @37
    @29
    ifnefalse
    eqeq2d
    biimpcd
    a1i
    ralimdva
    ralimdva
    ex
    com23
    rexlimdva
    imp
    sylbi
    chpscmat.d
    eleq2s
    3ad2ant1
    impcom
    cA
    @23
    cC
    cP
    cR
    cS
    vi
    vj
    vk
    cG
    cM
    c.mi
    cN
    cX
    @29
    chp0mat.c
    chp0mat.p
    chp0mat.a
    chpscmat.s
    @23
    eqid
    chp0mat.x
    @29
    eqid
    chp0mat.g
    chpscmat.m
    chpdmat
    syl31anc
    @10
    @16
    @20
    cG
    cgsu
    @10
    vk
    cN
    @15
    @19
    @10
    @12
    cN
    wcel
    #
    wa
    #
    @14
    @18
    cX
    c.mi
    @55
    @13
    cE
    cS
    @10
    @54
    @13
    cE
    wceq
    #
    @9
    @54
    @56
    wi
    #
    @2
    @8
    @3
    @57
    @4
    @7
    @56
    vn
    @12
    cN
    vn
    vk
    weq
    #
    @6
    @13
    cE
    @58
    @5
    @12
    @5
    @12
    cM
    @58
    id
    #
    @59
    oveq12d
    eqeq1d
    rspccv
    3ad2ant3
    adantl
    imp
    fveq2d
    oveq2d
    mpteq2dva
    oveq2d
    @10
    cG
    cmnd
    wcel
    #
    @0
    @19
    cG
    cbs
    cfv
    #
    wcel
    @21
    @22
    wceq
    @1
    @60
    @0
    @9
    @1
    cP
    ccrg
    wcel
    cG
    ccmn
    wcel
    @60
    cP
    cR
    chp0mat.p
    ply1crng
    cP
    cG
    chp0mat.g
    crngmgp
    cG
    cmnmnd
    3syl
    ad2antlr
    @34
    @10
    @19
    cP
    cbs
    cfv
    #
    @61
    @10
    cP
    cgrp
    wcel
    #
    cX
    @62
    wcel
    #
    @18
    @62
    wcel
    #
    @19
    @62
    wcel
    @1
    @63
    @0
    @9
    @1
    cP
    crg
    wcel
    #
    @63
    @1
    cR
    crg
    wcel
    #
    @66
    cR
    crngring
    #
    cP
    cR
    chp0mat.p
    ply1ring
    syl
    #
    cP
    ringgrp
    syl
    ad2antlr
    @1
    @64
    @0
    @9
    @1
    @67
    @64
    @68
    @62
    cP
    cR
    cX
    chp0mat.x
    chp0mat.p
    @62
    eqid
    #
    vr1cl
    syl
    ad2antlr
    @9
    @2
    @65
    @3
    @4
    @8
    @2
    @65
    wi
    @3
    @2
    @8
    @4
    @65
    @3
    @2
    @8
    @4
    @65
    wi
    wi
    @3
    @2
    wa
    #
    @4
    @8
    @65
    @71
    @4
    @8
    @65
    wi
    @71
    @4
    wa
    #
    @7
    @65
    vn
    cI
    cN
    @71
    @4
    simpr
    #
    @72
    @5
    cI
    wceq
    #
    wa
    @7
    @65
    wi
    #
    cI
    cI
    cM
    co
    #
    cE
    wceq
    #
    @65
    wi
    #
    @72
    @78
    @74
    @72
    @65
    @77
    @76
    cS
    cfv
    #
    @62
    wcel
    @72
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    @62
    @76
    cS
    @72
    cS
    @62
    @80
    @81
    cP
    chpscmat.s
    @80
    eqid
    @71
    @66
    @4
    @1
    @66
    @3
    @0
    @69
    ad2antll
    adantr
    @71
    cP
    clmod
    wcel
    #
    @4
    @1
    @82
    @3
    @0
    @1
    @67
    @82
    @68
    cP
    cR
    chp0mat.p
    ply1lmod
    syl
    ad2antll
    adantr
    @81
    eqid
    @70
    asclf
    @72
    @76
    @41
    @81
    @72
    @4
    @4
    @24
    @76
    @41
    wcel
    @73
    @73
    @71
    @24
    @4
    @3
    @24
    @2
    @44
    adantr
    adantr
    cA
    cR
    cI
    cI
    @41
    cM
    cN
    chp0mat.a
    @41
    eqid
    matecl
    syl3anc
    @72
    @80
    cR
    cbs
    @72
    cR
    @80
    @71
    cR
    @80
    wceq
    #
    @4
    @1
    @83
    @3
    @0
    cP
    cR
    ccrg
    chp0mat.p
    ply1sca
    ad2antll
    adantr
    eqcomd
    fveq2d
    eleqtrrd
    ffvelrnd
    @77
    @18
    @79
    @62
    @18
    @79
    wceq
    cE
    @76
    cE
    @76
    cS
    fveq2
    eqcoms
    eleq1d
    syl5ibrcom
    adantr
    @74
    @75
    @78
    wb
    @72
    @74
    @7
    @77
    @65
    @74
    @6
    @76
    cE
    @74
    @5
    cI
    @5
    cI
    cM
    @74
    id
    #
    @84
    oveq12d
    eqeq1d
    imbi1d
    adantl
    mpbird
    rspcimdv
    ex
    com23
    ex
    com24
    3imp
    impcom
    @62
    cP
    c.mi
    cX
    @18
    @70
    chpscmat.m
    grpsubcl
    syl3anc
    @62
    cP
    cG
    chp0mat.g
    @70
    mgpbas
    syl6eleq
    cN
    @61
    c.ex
    vk
    cG
    @19
    @61
    eqid
    chp0mat.m
    gsumconst
    syl3anc
    3eqtrd
end
