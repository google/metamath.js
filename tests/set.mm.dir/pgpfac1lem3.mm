include "csn.mm"
include "cfv.mm"
include "co.mm"
include "csubg.mm"
include "wcel.mm"
include "cin.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "cabl.mm"
include "cmre.mm"
include "cgrp.mm"
include "cacs.mm"
include "ablgrp.mm"
include "syl.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "wss.mm"
include "subgss.mm"
include "cdiv.mm"
include "cplusg.mm"
include "eldifad.mm"
include "sseldd.mm"
include "mrcsncl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "lsmub1.mm"
include "sstrd.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "pgpfac1lem3a.mm"
include "simprd.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "cprime.mm"
include "cpgp.mm"
include "pgpprm.mm"
include "prmz.mm"
include "cn.mm"
include "prmnn.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "snssd.mm"
include "mrcssidd.mm"
include "syl6sseqr.mm"
include "snssg.mm"
include "mpbird.mm"
include "subgmulgcl.mm"
include "eqid.mm"
include "subgcl.mm"
include "lsmsubg2.mm"
include "csg.mm"
include "lsmelvalm.mm"
include "cmpt.mm"
include "crn.mm"
include "cycsubg2.mm"
include "rexeqdv.mm"
include "cvv.mm"
include "wral.mm"
include "ovex.mm"
include "rgenw.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rexrnmpt.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "bitrd.mm"
include "adantr.mm"
include "simpr.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "cmul.mm"
include "simplrr.mm"
include "zcnd.mm"
include "cc.mm"
include "nncnd.mm"
include "divcan1d.mm"
include "oveq1d.mm"
include "wn.mm"
include "eldifbd.mm"
include "wi.mm"
include "subgsubcl.mm"
include "3expia.mm"
include "impancom.mm"
include "oveq1i.mm"
include "grppncan.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "mtod.mm"
include "cgcd.mm"
include "c1.mm"
include "coprm.mm"
include "caddc.mm"
include "bezout.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "syl5ibcom.mm"
include "simprl.mm"
include "zmulcld.mm"
include "simprr.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "mulcomd.mm"
include "mulgass.mm"
include "eqtrd.mm"
include "lsmub2.mm"
include "oveq2i.mm"
include "mulgdi.mm"
include "divcan2d.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "eqeltrd.mm"
include "ad2antll.mm"
include "mulgcl.mm"
include "ablnncan.mm"
include "sselda.mm"
include "ad2antrr.mm"
include "eqeltrrd.mm"
include "oveq1.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syld.mm"
include "mulg1.mm"
include "sylbid.mm"
include "mt3d.mm"
include "ex.mm"
include "imdistanda.mm"
include "elin.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "sseqtrd.mm"
include "subg0cl.mm"
include "elind.mm"
include "eqssd.mm"
include "lsmass.mm"
include "cdif.mm"
include "eldifd.mm"
include "pgpfac1lem1.mm"
include "mpdan.mm"
include "ineq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem pgpfac1lem3
  let wph: wff ph
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let c.po: class .(+)
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cG: class G
  let cK: class K
  let cM: class M
  let cO: class O
  let cW: class W
  let c.0: class .0.
  let vb: setvar b
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vn: setvar n
  assume pgpfac1.k: |- K = ( mrCls ` ( SubGrp ` G ) )
  assume pgpfac1.s: |- S = ( K ` { A } )
  assume pgpfac1.b: |- B = ( Base ` G )
  assume pgpfac1.o: |- O = ( od ` G )
  assume pgpfac1.e: |- E = ( gEx ` G )
  assume pgpfac1.z: |- .0. = ( 0g ` G )
  assume pgpfac1.l: |- .(+) = ( LSSum ` G )
  assume pgpfac1.p: |- ( ph -> P pGrp G )
  assume pgpfac1.g: |- ( ph -> G e. Abel )
  assume pgpfac1.n: |- ( ph -> B e. Fin )
  assume pgpfac1.oe: |- ( ph -> ( O ` A ) = E )
  assume pgpfac1.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pgpfac1.au: |- ( ph -> A e. U )
  assume pgpfac1.w: |- ( ph -> W e. ( SubGrp ` G ) )
  assume pgpfac1.i: |- ( ph -> ( S i^i W ) = { .0. } )
  assume pgpfac1.ss: |- ( ph -> ( S .(+) W ) C_ U )
  assume pgpfac1.2: |- ( ph -> A. w e. ( SubGrp ` G ) ( ( w C. U /\ A e. w ) -> -. ( S .(+) W ) C. w ) )
  assume pgpfac1.c: |- ( ph -> C e. ( U \ ( S .(+) W ) ) )
  assume pgpfac1.mg: |- .x. = ( .g ` G )
  assume pgpfac1.m: |- ( ph -> M e. ZZ )
  assume pgpfac1.mw: |- ( ph -> ( ( P .x. C ) ( +g ` G ) ( M .x. A ) ) e. W )
  assume pgpfac1.d: |- D = ( C ( +g ` G ) ( ( M / P ) .x. A ) )

  disjoint .0. t
  disjoint t w
  disjoint A t
  disjoint A w
  disjoint D t
  disjoint D w
  disjoint .(+) t
  disjoint .(+) w
  disjoint P t
  disjoint P w
  disjoint B t
  disjoint G t
  disjoint G w
  disjoint U t
  disjoint U w
  disjoint C t
  disjoint C w
  disjoint S t
  disjoint S w
  disjoint W t
  disjoint W w
  disjoint ph t
  disjoint ph w
  disjoint .x. t
  disjoint .x. w
  disjoint K t
  disjoint K w
  disjoint b k
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint .0. b
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint .0. k
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint .0. s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint .0. u
  disjoint v x
  disjoint v y
  disjoint .0. v
  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint b w
  disjoint A b
  disjoint k w
  disjoint A k
  disjoint s w
  disjoint A s
  disjoint u w
  disjoint A u
  disjoint v w
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint D a
  disjoint b n
  disjoint D b
  disjoint n t
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint .(+) a
  disjoint .(+) b
  disjoint .(+) k
  disjoint .(+) s
  disjoint .(+) u
  disjoint .(+) v
  disjoint .(+) x
  disjoint .(+) y
  disjoint E k
  disjoint O a
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P s
  disjoint P y
  disjoint B a
  disjoint k n
  disjoint B k
  disjoint n s
  disjoint n v
  disjoint B n
  disjoint B s
  disjoint B v
  disjoint G a
  disjoint G b
  disjoint G k
  disjoint n u
  disjoint G n
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint U b
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint U y
  disjoint C a
  disjoint C k
  disjoint C s
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint S n
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint W a
  disjoint W b
  disjoint W k
  disjoint W n
  disjoint W s
  disjoint W x
  disjoint W y
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint n ph
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint .x. a
  disjoint .x. b
  disjoint .x. k
  disjoint .x. n
  disjoint .x. s
  disjoint .x. y
  disjoint K s
  disjoint K x
  disjoint K y
  assert |- ( ph -> E. t e. ( SubGrp ` G ) ( ( S i^i t ) = { .0. } /\ ( S .(+) t ) = U ) )

  proof
    wph
    cW
    cD
    csn
    cK
    cfv
    #
    c.po
    co
    #
    cG
    csubg
    cfv
    #
    wcel
    #
    cS
    @1
    cin
    #
    c.0
    csn
    #
    wceq
    #
    cS
    @1
    c.po
    co
    #
    cU
    wceq
    #
    cS
    vt
    cv
    #
    cin
    #
    @5
    wceq
    #
    cS
    @9
    c.po
    co
    #
    cU
    wceq
    #
    wa
    #
    vt
    @2
    wrex
    wph
    cG
    cabl
    wcel
    #
    cW
    @2
    wcel
    #
    @0
    @2
    wcel
    #
    @3
    pgpfac1.g
    pgpfac1.w
    wph
    @2
    cB
    cmre
    cfv
    wcel
    #
    cD
    cB
    wcel
    #
    @17
    wph
    cG
    cgrp
    wcel
    #
    @2
    cB
    cacs
    cfv
    wcel
    @18
    wph
    @15
    @20
    pgpfac1.g
    cG
    ablgrp
    syl
    #
    cB
    cG
    pgpfac1.b
    subgacs
    @2
    cB
    acsmre
    3syl
    #
    wph
    cU
    cB
    cD
    wph
    cU
    @2
    wcel
    #
    cU
    cB
    wss
    pgpfac1.u
    cB
    cU
    cG
    pgpfac1.b
    subgss
    syl
    #
    wph
    cD
    cC
    cM
    cP
    cdiv
    co
    #
    cA
    c.x
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cU
    pgpfac1.d
    wph
    @23
    cC
    cU
    wcel
    @26
    cU
    wcel
    @28
    cU
    wcel
    pgpfac1.u
    wph
    cC
    cU
    cS
    cW
    c.po
    co
    #
    pgpfac1.c
    eldifad
    #
    wph
    cS
    cU
    @26
    wph
    cS
    @29
    cU
    wph
    cS
    @2
    wcel
    #
    @16
    cS
    @29
    wss
    wph
    cS
    cA
    csn
    #
    cK
    cfv
    #
    @2
    pgpfac1.s
    wph
    @18
    cA
    cB
    wcel
    #
    @33
    @2
    wcel
    @22
    wph
    cU
    cB
    cA
    @24
    pgpfac1.au
    sseldd
    #
    @2
    cA
    cK
    cB
    pgpfac1.k
    mrcsncl
    syl2anc
    syl5eqel
    #
    pgpfac1.w
    c.po
    cS
    cW
    cG
    pgpfac1.l
    lsmub1
    syl2anc
    #
    pgpfac1.ss
    sstrd
    wph
    @31
    @25
    cz
    wcel
    #
    cA
    cS
    wcel
    #
    @26
    cS
    wcel
    @36
    wph
    cP
    cM
    cdvds
    wbr
    #
    @38
    wph
    cP
    cE
    cdvds
    wbr
    @40
    wph
    vw
    cA
    cB
    cC
    cP
    c.po
    cS
    c.x
    cU
    cE
    cG
    cK
    cM
    cO
    cW
    c.0
    pgpfac1.k
    pgpfac1.s
    pgpfac1.b
    pgpfac1.o
    pgpfac1.e
    pgpfac1.z
    pgpfac1.l
    pgpfac1.p
    pgpfac1.g
    pgpfac1.n
    pgpfac1.oe
    pgpfac1.u
    pgpfac1.au
    pgpfac1.w
    pgpfac1.i
    pgpfac1.ss
    pgpfac1.2
    pgpfac1.c
    pgpfac1.mg
    pgpfac1.m
    pgpfac1.mw
    pgpfac1lem3a
    simprd
    wph
    cP
    cz
    wcel
    #
    cP
    cc0
    wne
    #
    cM
    cz
    wcel
    @40
    @38
    wb
    wph
    cP
    cprime
    wcel
    #
    @41
    wph
    cP
    cG
    cpgp
    wbr
    @43
    pgpfac1.p
    cP
    cG
    pgpprm
    syl
    #
    cP
    prmz
    syl
    #
    wph
    cP
    wph
    @43
    cP
    cn
    wcel
    @44
    cP
    prmnn
    syl
    #
    nnne0d
    #
    pgpfac1.m
    cP
    cM
    dvdsval2
    syl3anc
    mpbid
    #
    wph
    @39
    @32
    cS
    wss
    #
    wph
    @32
    @33
    cS
    wph
    @2
    @32
    cK
    cB
    @22
    pgpfac1.k
    wph
    cA
    cB
    @35
    snssd
    mrcssidd
    pgpfac1.s
    syl6sseqr
    wph
    cA
    cU
    wcel
    @39
    @49
    wb
    pgpfac1.au
    cA
    cS
    cU
    snssg
    syl
    mpbird
    cS
    c.x
    cG
    @25
    cA
    pgpfac1.mg
    subgmulgcl
    syl3anc
    #
    sseldd
    @27
    cU
    cG
    cC
    @26
    @27
    eqid
    #
    subgcl
    syl3anc
    syl5eqel
    #
    sseldd
    #
    @2
    cD
    cK
    cB
    pgpfac1.k
    mrcsncl
    syl2anc
    #
    c.po
    cW
    @0
    cG
    pgpfac1.l
    lsmsubg2
    syl3anc
    #
    wph
    @4
    @5
    wph
    @4
    cS
    cW
    cin
    #
    @5
    wph
    vx
    @4
    @56
    wph
    vx
    cv
    #
    cS
    wcel
    #
    @57
    @1
    wcel
    #
    wa
    @58
    @57
    cW
    wcel
    #
    wa
    @57
    @4
    wcel
    @57
    @56
    wcel
    wph
    @58
    @59
    @60
    wph
    @58
    wa
    #
    @59
    @57
    vw
    cv
    #
    vn
    cv
    #
    cD
    c.x
    co
    #
    cG
    csg
    cfv
    #
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    vw
    cW
    wrex
    #
    @60
    wph
    @59
    @69
    wb
    @58
    wph
    @59
    @57
    @62
    vy
    cv
    #
    @65
    co
    #
    wceq
    #
    vy
    @0
    wrex
    #
    vw
    cW
    wrex
    @69
    wph
    vw
    vy
    c.po
    cW
    @0
    cG
    @65
    @57
    @65
    eqid
    #
    pgpfac1.l
    pgpfac1.w
    @54
    lsmelvalm
    wph
    @73
    @68
    vw
    cW
    wph
    @73
    @72
    vy
    vn
    cz
    @64
    cmpt
    #
    crn
    #
    wrex
    #
    @68
    wph
    @72
    vy
    @0
    @76
    wph
    @20
    @19
    @0
    @76
    wceq
    @21
    @53
    vn
    cD
    c.x
    @75
    cG
    cK
    cB
    pgpfac1.b
    pgpfac1.mg
    @75
    eqid
    #
    pgpfac1.k
    cycsubg2
    syl2anc
    rexeqdv
    @64
    cvv
    wcel
    #
    vn
    cz
    wral
    @77
    @68
    wb
    @79
    vn
    cz
    @63
    cD
    c.x
    ovex
    rgenw
    @72
    @67
    vn
    vy
    cz
    @64
    @75
    cvv
    @78
    @70
    @64
    wceq
    @71
    @66
    @57
    @70
    @64
    @62
    @65
    oveq2
    eqeq2d
    rexrnmpt
    ax-mp
    syl6bb
    rexbidv
    bitrd
    adantr
    @61
    @67
    @60
    vw
    vn
    cW
    cz
    @61
    @62
    cW
    wcel
    #
    @63
    cz
    wcel
    #
    wa
    #
    wa
    #
    @67
    @60
    @83
    @67
    wa
    #
    @57
    @66
    cW
    @83
    @67
    simpr
    #
    @84
    @16
    @80
    @64
    cW
    wcel
    @66
    cW
    wcel
    wph
    @16
    @58
    @82
    @67
    pgpfac1.w
    ad3antrrr
    #
    @61
    @80
    @81
    @67
    simplrl
    #
    @84
    @64
    @63
    cP
    cdiv
    co
    #
    cP
    cD
    c.x
    co
    #
    c.x
    co
    #
    cW
    @84
    @88
    cP
    cmul
    co
    #
    cD
    c.x
    co
    #
    @64
    @90
    @84
    @91
    @63
    cD
    c.x
    @84
    @63
    cP
    @84
    @63
    @61
    @80
    @81
    @67
    simplrr
    #
    zcnd
    #
    wph
    cP
    cc
    wcel
    #
    @58
    @82
    @67
    wph
    cP
    @46
    nncnd
    #
    ad3antrrr
    #
    wph
    @42
    @58
    @82
    @67
    @47
    ad3antrrr
    #
    divcan1d
    oveq1d
    @84
    @20
    @88
    cz
    wcel
    #
    @41
    @19
    @92
    @90
    wceq
    wph
    @20
    @58
    @82
    @67
    @21
    ad3antrrr
    #
    @84
    cP
    @63
    cdvds
    wbr
    #
    @99
    @84
    @101
    cD
    @29
    wcel
    #
    wph
    @102
    wn
    @58
    @82
    @67
    wph
    @102
    cC
    @29
    wcel
    #
    wph
    cC
    cU
    @29
    pgpfac1.c
    eldifbd
    wph
    @102
    cD
    @26
    @65
    co
    #
    @29
    wcel
    #
    @103
    wph
    @29
    @2
    wcel
    #
    @26
    @29
    wcel
    #
    @102
    @105
    wi
    wph
    @15
    @31
    @16
    @106
    pgpfac1.g
    @36
    pgpfac1.w
    c.po
    cS
    cW
    cG
    pgpfac1.l
    lsmsubg2
    syl3anc
    #
    wph
    cS
    @29
    @26
    @37
    @50
    sseldd
    @106
    @102
    @107
    @105
    @106
    @102
    @107
    @105
    @29
    cG
    @65
    cD
    @26
    @74
    subgsubcl
    3expia
    impancom
    syl2anc
    wph
    @104
    cC
    @29
    wph
    @104
    @28
    @26
    @65
    co
    #
    cC
    cD
    @28
    @26
    @65
    pgpfac1.d
    oveq1i
    wph
    @20
    cC
    cB
    wcel
    #
    @26
    cB
    wcel
    #
    @109
    cC
    wceq
    @21
    wph
    cU
    cB
    cC
    @24
    @30
    sseldd
    #
    wph
    cS
    cB
    @26
    wph
    @31
    cS
    cB
    wss
    @36
    cB
    cS
    cG
    pgpfac1.b
    subgss
    syl
    @50
    sseldd
    #
    cB
    @27
    cG
    @65
    cC
    @26
    pgpfac1.b
    @51
    @74
    grppncan
    syl3anc
    syl5eq
    eleq1d
    sylibd
    mtod
    #
    ad3antrrr
    @84
    @101
    wn
    #
    cP
    @63
    cgcd
    co
    #
    c1
    wceq
    #
    @102
    @84
    @43
    @81
    @115
    @117
    wb
    wph
    @43
    @58
    @82
    @67
    @44
    ad3antrrr
    @93
    cP
    @63
    coprm
    syl2anc
    @84
    @117
    c1
    cD
    c.x
    co
    #
    @29
    wcel
    #
    @102
    @84
    @117
    c1
    cP
    va
    cv
    #
    cmul
    co
    #
    @63
    vb
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    #
    @119
    @84
    @116
    @124
    wceq
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    #
    @117
    @126
    @84
    @41
    @81
    @128
    wph
    @41
    @58
    @82
    @67
    @45
    ad3antrrr
    #
    @93
    va
    vb
    cP
    @63
    bezout
    syl2anc
    @117
    @127
    @125
    va
    vb
    cz
    cz
    @116
    c1
    @124
    eqeq1
    2rexbidv
    syl5ibcom
    @84
    @125
    @119
    va
    vb
    cz
    cz
    @84
    @120
    cz
    wcel
    #
    @122
    cz
    wcel
    #
    wa
    #
    wa
    #
    @119
    @125
    @124
    cD
    c.x
    co
    #
    @29
    wcel
    @133
    @134
    @121
    cD
    c.x
    co
    #
    @123
    cD
    c.x
    co
    #
    @27
    co
    #
    @29
    @133
    @20
    @121
    cz
    wcel
    @123
    cz
    wcel
    @19
    @134
    @137
    wceq
    @84
    @20
    @132
    @100
    adantr
    #
    @133
    cP
    @120
    @84
    @41
    @132
    @129
    adantr
    #
    @84
    @130
    @131
    simprl
    #
    zmulcld
    @133
    @63
    @122
    @84
    @81
    @132
    @93
    adantr
    #
    @84
    @130
    @131
    simprr
    #
    zmulcld
    @84
    @19
    @132
    wph
    @19
    @58
    @82
    @67
    @53
    ad3antrrr
    #
    adantr
    #
    cB
    @27
    c.x
    cG
    @121
    @123
    cD
    pgpfac1.b
    pgpfac1.mg
    @51
    mulgdir
    syl13anc
    @133
    @106
    @135
    @29
    wcel
    @136
    @29
    wcel
    @137
    @29
    wcel
    @84
    @106
    @132
    wph
    @106
    @58
    @82
    @67
    @108
    ad3antrrr
    #
    adantr
    #
    @133
    @135
    @120
    @89
    c.x
    co
    #
    @29
    @133
    @135
    @120
    cP
    cmul
    co
    #
    cD
    c.x
    co
    #
    @147
    @133
    @121
    @148
    cD
    c.x
    @133
    cP
    @120
    @84
    @95
    @132
    @97
    adantr
    @130
    @120
    cc
    wcel
    @84
    @131
    @120
    zcn
    ad2antrl
    mulcomd
    oveq1d
    @133
    @20
    @130
    @41
    @19
    @149
    @147
    wceq
    @138
    @140
    @139
    @144
    cB
    c.x
    cG
    @120
    cP
    cD
    pgpfac1.b
    pgpfac1.mg
    mulgass
    syl13anc
    eqtrd
    @133
    @106
    @130
    @89
    @29
    wcel
    #
    @147
    @29
    wcel
    @146
    @140
    @84
    @150
    @132
    wph
    @150
    @58
    @82
    @67
    wph
    cW
    @29
    @89
    wph
    @31
    @16
    cW
    @29
    wss
    #
    @36
    pgpfac1.w
    c.po
    cS
    cW
    cG
    pgpfac1.l
    lsmub2
    syl2anc
    #
    wph
    @89
    cP
    cC
    c.x
    co
    #
    cM
    cA
    c.x
    co
    #
    @27
    co
    #
    cW
    wph
    @89
    @153
    cP
    @26
    c.x
    co
    #
    @27
    co
    #
    @155
    wph
    @89
    cP
    @28
    c.x
    co
    #
    @157
    cD
    @28
    cP
    c.x
    pgpfac1.d
    oveq2i
    wph
    @15
    @41
    @110
    @111
    @158
    @157
    wceq
    pgpfac1.g
    @45
    @112
    @113
    cB
    @27
    c.x
    cG
    cP
    cC
    @26
    pgpfac1.b
    pgpfac1.mg
    @51
    mulgdi
    syl13anc
    syl5eq
    wph
    @156
    @154
    @153
    @27
    wph
    cP
    @25
    cmul
    co
    #
    cA
    c.x
    co
    #
    @156
    @154
    wph
    @20
    @41
    @38
    @34
    @160
    @156
    wceq
    @21
    @45
    @48
    @35
    cB
    c.x
    cG
    cP
    @25
    cA
    pgpfac1.b
    pgpfac1.mg
    mulgass
    syl13anc
    wph
    @159
    cM
    cA
    c.x
    wph
    cM
    cP
    wph
    cM
    pgpfac1.m
    zcnd
    @96
    @47
    divcan2d
    oveq1d
    eqtr3d
    oveq2d
    eqtrd
    pgpfac1.mw
    eqeltrd
    #
    sseldd
    ad3antrrr
    adantr
    @29
    c.x
    cG
    @120
    @89
    pgpfac1.mg
    subgmulgcl
    syl3anc
    eqeltrd
    @133
    @136
    @122
    @64
    c.x
    co
    #
    @29
    @133
    @136
    @122
    @63
    cmul
    co
    #
    cD
    c.x
    co
    #
    @162
    @133
    @123
    @163
    cD
    c.x
    @133
    @63
    @122
    @84
    @63
    cc
    wcel
    @132
    @94
    adantr
    @131
    @122
    cc
    wcel
    @84
    @130
    @122
    zcn
    ad2antll
    mulcomd
    oveq1d
    @133
    @20
    @131
    @81
    @19
    @164
    @162
    wceq
    @138
    @142
    @141
    @144
    cB
    c.x
    cG
    @122
    @63
    cD
    pgpfac1.b
    pgpfac1.mg
    mulgass
    syl13anc
    eqtrd
    @133
    @106
    @131
    @64
    @29
    wcel
    #
    @162
    @29
    wcel
    @146
    @142
    @84
    @165
    @132
    @84
    @62
    @57
    @65
    co
    #
    @64
    @29
    @84
    @166
    @62
    @66
    @65
    co
    @64
    @84
    @57
    @66
    @62
    @65
    @85
    oveq2d
    @84
    cB
    cG
    @65
    @62
    @64
    pgpfac1.b
    @74
    wph
    @15
    @58
    @82
    @67
    pgpfac1.g
    ad3antrrr
    @84
    cW
    cB
    @62
    @84
    @16
    cW
    cB
    wss
    @86
    cB
    cW
    cG
    pgpfac1.b
    subgss
    syl
    @87
    sseldd
    @84
    @20
    @81
    @19
    @64
    cB
    wcel
    @100
    @93
    @143
    cB
    c.x
    cG
    @63
    cD
    pgpfac1.b
    pgpfac1.mg
    mulgcl
    syl3anc
    ablnncan
    eqtrd
    @84
    @106
    @62
    @29
    wcel
    @57
    @29
    wcel
    #
    @166
    @29
    wcel
    @145
    @84
    cW
    @29
    @62
    wph
    @151
    @58
    @82
    @67
    @152
    ad3antrrr
    @87
    sseldd
    @61
    @167
    @82
    @67
    wph
    cS
    @29
    @57
    @37
    sselda
    ad2antrr
    @29
    cG
    @65
    @62
    @57
    @74
    subgsubcl
    syl3anc
    eqeltrrd
    adantr
    @29
    c.x
    cG
    @122
    @64
    pgpfac1.mg
    subgmulgcl
    syl3anc
    eqeltrd
    @27
    @29
    cG
    @135
    @136
    @51
    subgcl
    syl3anc
    eqeltrd
    @125
    @118
    @134
    @29
    c1
    @124
    cD
    c.x
    oveq1
    eleq1d
    syl5ibrcom
    rexlimdvva
    syld
    @84
    @118
    cD
    @29
    @84
    @19
    @118
    cD
    wceq
    @143
    cB
    c.x
    cG
    cD
    pgpfac1.b
    pgpfac1.mg
    mulg1
    syl
    eleq1d
    sylibd
    sylbid
    mt3d
    @84
    @41
    @42
    @81
    @101
    @99
    wb
    @129
    @98
    @93
    cP
    @63
    dvdsval2
    syl3anc
    mpbid
    #
    @129
    @143
    cB
    c.x
    cG
    @88
    cP
    cD
    pgpfac1.b
    pgpfac1.mg
    mulgass
    syl13anc
    eqtr3d
    @84
    @16
    @99
    @89
    cW
    wcel
    #
    @90
    cW
    wcel
    @86
    @168
    wph
    @169
    @58
    @82
    @67
    @161
    ad3antrrr
    cW
    c.x
    cG
    @88
    @89
    pgpfac1.mg
    subgmulgcl
    syl3anc
    eqeltrd
    cW
    cG
    @65
    @62
    @64
    @74
    subgsubcl
    syl3anc
    eqeltrd
    ex
    rexlimdvva
    sylbid
    imdistanda
    @57
    cS
    @1
    elin
    @57
    cS
    cW
    elin
    3imtr4g
    ssrdv
    pgpfac1.i
    sseqtrd
    wph
    c.0
    @4
    wph
    cS
    @1
    c.0
    wph
    @31
    c.0
    cS
    wcel
    @36
    cS
    cG
    c.0
    pgpfac1.z
    subg0cl
    syl
    wph
    @3
    c.0
    @1
    wcel
    @55
    @1
    cG
    c.0
    pgpfac1.z
    subg0cl
    syl
    elind
    snssd
    eqssd
    wph
    @29
    @0
    c.po
    co
    #
    @7
    cU
    wph
    @31
    @16
    @17
    @170
    @7
    wceq
    @36
    pgpfac1.w
    @54
    c.po
    cS
    cW
    @0
    cG
    pgpfac1.l
    lsmass
    syl3anc
    wph
    cD
    cU
    @29
    cdif
    wcel
    @170
    cU
    wceq
    wph
    cD
    cU
    @29
    @52
    @114
    eldifd
    wph
    vw
    cA
    cB
    cD
    cP
    c.po
    cS
    cU
    cE
    cG
    cK
    cO
    cW
    c.0
    pgpfac1.k
    pgpfac1.s
    pgpfac1.b
    pgpfac1.o
    pgpfac1.e
    pgpfac1.z
    pgpfac1.l
    pgpfac1.p
    pgpfac1.g
    pgpfac1.n
    pgpfac1.oe
    pgpfac1.u
    pgpfac1.au
    pgpfac1.w
    pgpfac1.i
    pgpfac1.ss
    pgpfac1.2
    pgpfac1lem1
    mpdan
    eqtr3d
    @14
    @6
    @8
    wa
    vt
    @1
    @2
    @9
    @1
    wceq
    #
    @11
    @6
    @13
    @8
    @171
    @10
    @4
    @5
    @9
    @1
    cS
    ineq2
    eqeq1d
    @171
    @12
    @7
    cU
    @9
    @1
    cS
    c.po
    oveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
end
