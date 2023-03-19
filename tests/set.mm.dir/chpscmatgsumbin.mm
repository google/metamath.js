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
include "chash.mm"
include "cplusg.mm"
include "cc0.mm"
include "cfz.mm"
include "cbc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "chpscmat0.mm"
include "cminusg.mm"
include "cbs.mm"
include "crg.mm"
include "crngring.mm"
include "adantl.mm"
include "eqid.mm"
include "vr1cl.mm"
include "syl.mm"
include "adantr.mm"
include "csca.mm"
include "wf.mm"
include "ad2antlr.mm"
include "ply1ring.mm"
include "ply1lmod.mm"
include "asclf.mm"
include "simpr2.mm"
include "wi.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "wrex.mm"
include "crab.mm"
include "elrabi.mm"
include "a1d.mm"
include "eleq2s.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "matecl.mm"
include "syl3anc.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "clmod.mm"
include "asclinvg.mm"
include "syl5req.mm"
include "fveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cmulr.mm"
include "cn0.mm"
include "simplr.mm"
include "hashcl.mm"
include "ad2antrr.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpinvcl.mm"
include "lply1binomsc.mm"
include "casa.mm"
include "ply1assa.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "fznn0sub.mm"
include "mgpbas.mm"
include "syl6eleq.mm"
include "mulgnn0cl.mm"
include "syl6eq.mm"
include "3syl.mm"
include "elfznn0.mm"
include "adantlr.mm"
include "asclmul1.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"

theorem chpscmatgsumbin
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let vc: setvar c
  let vl: setvar l
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
  assume chpscmatgsum.f: |- F = ( .g ` P )
  assume chpscmatgsum.h: |- H = ( mulGrp ` R )
  assume chpscmatgsum.e: |- E = ( .g ` H )
  assume chpscmatgsum.i: |- I = ( invg ` R )
  assume chpscmatgsum.s: |- .x. = ( .s ` P )

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
  disjoint D l
  disjoint F l
  disjoint I l
  disjoint J l
  disjoint J n
  disjoint l n
  disjoint M l
  disjoint N l
  disjoint P l
  disjoint R l
  disjoint S l
  disjoint X l
  disjoint .^ l
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
  assert |- ( ( ( N e. Fin /\ R e. CRing ) /\ ( M e. D /\ J e. N /\ A. n e. N ( n M n ) = ( J M J ) ) ) -> ( C ` M ) = ( P gsum ( l e. ( 0 ... ( # ` N ) ) |-> ( ( ( # ` N ) _C l ) F ( ( ( ( # ` N ) - l ) E ( I ` ( J M J ) ) ) .x. ( l .^ X ) ) ) ) ) )

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
    cJ
    cN
    wcel
    #
    vn
    cv
    #
    @5
    cM
    co
    cJ
    cJ
    cM
    co
    #
    wceq
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
    cN
    chash
    cfv
    #
    cX
    @6
    cS
    cfv
    #
    c.mi
    co
    #
    c.ex
    co
    @10
    cX
    @6
    cI
    cfv
    #
    cS
    cfv
    #
    cP
    cplusg
    cfv
    #
    co
    #
    c.ex
    co
    #
    cP
    vl
    cc0
    @10
    cfz
    co
    #
    @10
    vl
    cv
    #
    cbc
    co
    #
    @10
    @19
    cmin
    co
    #
    @13
    cE
    co
    #
    @19
    cX
    c.ex
    co
    #
    c.x
    co
    #
    cF
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cA
    cC
    cD
    cP
    cR
    cS
    vi
    vj
    vm
    vn
    c.ex
    cG
    cJ
    cM
    c.mi
    cN
    cX
    vc
    chp0mat.c
    chp0mat.p
    chp0mat.a
    chp0mat.x
    chp0mat.g
    chp0mat.m
    chpscmat.d
    chpscmat.s
    chpscmat.m
    chpscmat0
    @9
    @12
    @16
    @10
    c.ex
    @9
    @12
    cX
    @11
    cP
    cminusg
    cfv
    #
    cfv
    #
    @15
    co
    #
    @16
    @9
    cX
    cP
    cbs
    cfv
    #
    wcel
    #
    @11
    @31
    wcel
    @12
    @30
    wceq
    @2
    @32
    @8
    @2
    cR
    crg
    wcel
    #
    @32
    @1
    @33
    @0
    cR
    crngring
    #
    adantl
    #
    @31
    cP
    cR
    cX
    chp0mat.x
    chp0mat.p
    @31
    eqid
    #
    vr1cl
    syl
    #
    adantr
    @9
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    @31
    @6
    cS
    @9
    @33
    @39
    @31
    cS
    wf
    @1
    @33
    @0
    @8
    @34
    ad2antlr
    @33
    cS
    @31
    @38
    @39
    cP
    chpscmat.s
    @38
    eqid
    #
    cP
    cR
    chp0mat.p
    ply1ring
    #
    cP
    cR
    chp0mat.p
    ply1lmod
    #
    @39
    eqid
    #
    @36
    asclf
    syl
    @9
    @6
    cR
    cbs
    cfv
    #
    @39
    @9
    @4
    @4
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    @6
    @44
    wcel
    #
    @2
    @3
    @4
    @7
    simpr2
    #
    @48
    @8
    @2
    @46
    @3
    @4
    @2
    @46
    wi
    #
    @7
    @49
    cM
    vi
    cv
    vj
    cv
    vm
    cv
    co
    vi
    vj
    weq
    vc
    cv
    cR
    c0g
    cfv
    cif
    wceq
    vj
    cN
    wral
    vi
    cN
    wral
    vc
    @44
    wrex
    #
    vm
    @45
    crab
    #
    cD
    cM
    @51
    wcel
    @46
    @2
    @50
    vm
    cM
    @45
    elrabi
    a1d
    chpscmat.d
    eleq2s
    3ad2ant1
    impcom
    cA
    cR
    cJ
    cJ
    @44
    cM
    cN
    chp0mat.a
    @44
    eqid
    #
    matecl
    syl3anc
    #
    @9
    @38
    cR
    cbs
    @2
    @38
    cR
    wceq
    @8
    @2
    cR
    @38
    @1
    cR
    @38
    wceq
    @0
    cP
    cR
    ccrg
    chp0mat.p
    ply1sca
    adantl
    #
    eqcomd
    #
    adantr
    fveq2d
    eleqtrrd
    #
    ffvelrnd
    @31
    @15
    cP
    @28
    c.mi
    cX
    @11
    @36
    @15
    eqid
    #
    @28
    eqid
    #
    chpscmat.m
    grpsubval
    syl2anc
    @9
    @29
    @14
    cX
    @15
    @9
    @29
    @6
    @38
    cminusg
    cfv
    #
    cfv
    #
    cS
    cfv
    #
    @14
    @9
    cP
    clmod
    wcel
    #
    cP
    crg
    wcel
    #
    @6
    @39
    wcel
    @29
    @61
    wceq
    @2
    @62
    @8
    @2
    @33
    @62
    @35
    @42
    syl
    adantr
    @2
    @63
    @8
    @2
    @33
    @63
    @35
    @41
    syl
    adantr
    @56
    cS
    @39
    @6
    @38
    @59
    @28
    cP
    chpscmat.s
    @40
    @43
    @59
    eqid
    @58
    asclinvg
    syl3anc
    @9
    @60
    @13
    cS
    @9
    @6
    @59
    cI
    @9
    cI
    cR
    cminusg
    cfv
    #
    @59
    chpscmatgsum.i
    @2
    @64
    @59
    wceq
    @8
    @2
    cR
    @38
    cminusg
    @54
    fveq2d
    adantr
    syl5req
    fveq1d
    fveq2d
    eqtrd
    oveq2d
    eqtrd
    oveq2d
    @9
    @17
    cP
    vl
    @18
    @20
    @22
    cS
    cfv
    @23
    cP
    cmulr
    cfv
    #
    co
    #
    cF
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @27
    @9
    @1
    @10
    cn0
    wcel
    #
    @13
    @44
    wcel
    #
    @17
    @69
    wceq
    @0
    @1
    @8
    simplr
    @0
    @70
    @1
    @8
    cN
    hashcl
    ad2antrr
    @9
    cR
    cgrp
    wcel
    #
    @47
    @71
    @1
    @72
    @0
    @8
    @1
    @33
    @72
    @34
    cR
    ringgrp
    syl
    ad2antlr
    @53
    @44
    cR
    cI
    @6
    @52
    chpscmatgsum.i
    grpinvcl
    syl2anc
    #
    @13
    cP
    @15
    cR
    cS
    cF
    @65
    vl
    cE
    c.ex
    cG
    cH
    @44
    @10
    cX
    chp0mat.p
    chp0mat.x
    @57
    @65
    eqid
    #
    chpscmatgsum.f
    chp0mat.g
    chp0mat.m
    @52
    chpscmat.s
    chpscmatgsum.h
    chpscmatgsum.e
    lply1binomsc
    syl3anc
    @9
    @68
    @26
    cP
    cgsu
    @9
    vl
    @18
    @67
    @25
    @9
    @19
    @18
    wcel
    #
    wa
    #
    @66
    @24
    @20
    cF
    @76
    cP
    casa
    wcel
    #
    @22
    @39
    wcel
    @23
    @31
    wcel
    #
    @66
    @24
    wceq
    @2
    @77
    @8
    @75
    @1
    @77
    @0
    cP
    cR
    chp0mat.p
    ply1assa
    adantl
    ad2antrr
    @76
    @22
    cH
    cbs
    cfv
    #
    @39
    @76
    cH
    cmnd
    wcel
    #
    @21
    cn0
    wcel
    #
    @13
    @79
    wcel
    #
    @22
    @79
    wcel
    @2
    @80
    @8
    @75
    @2
    @33
    @80
    @35
    cR
    cH
    chpscmatgsum.h
    ringmgp
    syl
    ad2antrr
    @75
    @81
    @9
    @19
    cc0
    @10
    fznn0sub
    adantl
    @9
    @82
    @75
    @9
    @13
    @44
    @79
    @73
    @44
    cR
    cH
    chpscmatgsum.h
    @52
    mgpbas
    #
    syl6eleq
    adantr
    @79
    cE
    cH
    @21
    @13
    @79
    eqid
    chpscmatgsum.e
    mulgnn0cl
    syl3anc
    @2
    @39
    @79
    wceq
    @8
    @75
    @2
    @39
    @44
    @79
    @2
    @38
    cR
    cbs
    @55
    fveq2d
    @83
    syl6eq
    ad2antrr
    eleqtrrd
    @2
    @75
    @78
    @8
    @2
    @75
    wa
    cG
    cmnd
    wcel
    #
    @19
    cn0
    wcel
    #
    @32
    @78
    @1
    @84
    @0
    @75
    @1
    @33
    @63
    @84
    @34
    @41
    cP
    cG
    chp0mat.g
    ringmgp
    3syl
    ad2antlr
    @75
    @85
    @2
    @19
    @10
    elfznn0
    adantl
    @2
    @32
    @75
    @37
    adantr
    @31
    c.ex
    cG
    @19
    cX
    @31
    cP
    cG
    chp0mat.g
    @36
    mgpbas
    chp0mat.m
    mulgnn0cl
    syl3anc
    adantlr
    cS
    @22
    c.x
    @65
    @38
    @39
    @31
    cP
    @23
    chpscmat.s
    @40
    @43
    @36
    @74
    chpscmatgsum.s
    asclmul1
    syl3anc
    oveq2d
    mpteq2dva
    oveq2d
    eqtrd
    3eqtrd
end
