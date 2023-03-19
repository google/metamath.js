include "co.mm"
include "wcel.mm"
include "eldifbd.mm"
include "wn.mm"
include "c1.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "cz.mm"
include "wrex.mm"
include "csn.mm"
include "cfv.mm"
include "wa.mm"
include "eldifad.mm"
include "adantr.mm"
include "cdif.mm"
include "wceq.mm"
include "csubg.mm"
include "cprime.mm"
include "cpgp.mm"
include "wbr.mm"
include "pgpprm.mm"
include "syl.mm"
include "prmz.mm"
include "subgmulgcl.mm"
include "syl3anc.mm"
include "simpr.mm"
include "eldifd.mm"
include "pgpfac1lem1.mm"
include "syldan.mm"
include "eleqtrrd.mm"
include "ex.mm"
include "csg.mm"
include "eqid.mm"
include "cabl.mm"
include "cmre.mm"
include "cgrp.mm"
include "cacs.mm"
include "ablgrp.mm"
include "subgacs.mm"
include "acsmred.mm"
include "wss.mm"
include "subgss.mm"
include "sseldd.mm"
include "mrcsncl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "lsmsubg2.mm"
include "lsmelvalm.mm"
include "cmpt.mm"
include "crn.mm"
include "cycsubg2.mm"
include "rexeqdv.mm"
include "cvv.mm"
include "wral.mm"
include "wb.mm"
include "ovex.mm"
include "rgenw.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rexrnmpt.mm"
include "mp1i.mm"
include "bitrd.mm"
include "rexbidv.mm"
include "rexcom.mm"
include "cplusg.mm"
include "ad2antrr.mm"
include "sstrd.mm"
include "sselda.mm"
include "simplr.mm"
include "mulgcl.mm"
include "grpsubadd.mm"
include "syl13anc.mm"
include "1zzd.mm"
include "zmulcld.mm"
include "mulgdir.mm"
include "mulg1.mm"
include "mulgass.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "bitr4d.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "rexbidva.mm"
include "risset.mm"
include "syl6bbr.mm"
include "syl5bb.mm"
include "3bitrd.mm"
include "sylibd.mm"
include "wi.mm"
include "cgcd.mm"
include "1z.mm"
include "id.mm"
include "zmulcl.mm"
include "syl2anr.mm"
include "zaddcl.mm"
include "sylancr.mm"
include "chash.mm"
include "cdvds.mm"
include "cn0.mm"
include "odcl.mm"
include "nn0zd.mm"
include "cfn.mm"
include "hashcl.mm"
include "cpc.mm"
include "cexp.mm"
include "gcdcom.mm"
include "pgphash.mm"
include "oveq1d.mm"
include "gcdaddm.mm"
include "gcd1.mm"
include "eqtr3d.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "pccld.mm"
include "rpexp1i.mm"
include "mpd.mm"
include "3eqtrd.mm"
include "oddvds2.mm"
include "rpdvds.mm"
include "syl32anc.mm"
include "odbezout.mm"
include "syl31anc.mm"
include "3expia.mm"
include "eleq1.mm"
include "imbi2d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "syld.mm"
include "mt3d.mm"

theorem pgpfac1lem2
  let wph: wff ph
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.po: class .(+)
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cG: class G
  let cK: class K
  let cO: class O
  let cW: class W
  let c.0: class .0.
  let vb: setvar b
  let vk: setvar k
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vn: setvar n
  let cD: class D
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

  disjoint A w
  disjoint .(+) w
  disjoint P w
  disjoint G w
  disjoint U w
  disjoint C w
  disjoint S w
  disjoint W w
  disjoint ph w
  disjoint .x. w
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
  disjoint .0. t
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
  disjoint t w
  disjoint A t
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
  disjoint D t
  disjoint D w
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
  disjoint .(+) t
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
  disjoint P t
  disjoint P y
  disjoint B a
  disjoint k n
  disjoint B k
  disjoint n s
  disjoint n v
  disjoint B n
  disjoint B s
  disjoint B t
  disjoint B v
  disjoint G a
  disjoint G b
  disjoint G k
  disjoint n u
  disjoint G n
  disjoint G s
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint U b
  disjoint U k
  disjoint U s
  disjoint U t
  disjoint U u
  disjoint U v
  disjoint U y
  disjoint C a
  disjoint C k
  disjoint C s
  disjoint C t
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint S n
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint W a
  disjoint W b
  disjoint W k
  disjoint W n
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint .x. a
  disjoint .x. b
  disjoint .x. k
  disjoint .x. n
  disjoint .x. s
  disjoint .x. t
  disjoint .x. y
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  assert |- ( ph -> ( P .x. C ) e. ( S .(+) W ) )

  proof
    wph
    cP
    cC
    c.x
    co
    #
    cS
    cW
    c.po
    co
    #
    wcel
    #
    cC
    @1
    wcel
    #
    wph
    cC
    cU
    @1
    pgpfac1.c
    eldifbd
    wph
    @2
    wn
    #
    c1
    vk
    cv
    #
    cP
    cmul
    co
    #
    caddc
    co
    #
    cC
    c.x
    co
    #
    @1
    wcel
    #
    vk
    cz
    wrex
    #
    @3
    wph
    @4
    cC
    @1
    @0
    csn
    cK
    cfv
    #
    c.po
    co
    #
    wcel
    #
    @10
    wph
    @4
    @13
    wph
    @4
    wa
    #
    cC
    cU
    @12
    wph
    cC
    cU
    wcel
    #
    @4
    wph
    cC
    cU
    @1
    pgpfac1.c
    eldifad
    #
    adantr
    wph
    @4
    @0
    cU
    @1
    cdif
    wcel
    @12
    cU
    wceq
    @14
    @0
    cU
    @1
    wph
    @0
    cU
    wcel
    #
    @4
    wph
    cU
    cG
    csubg
    cfv
    #
    wcel
    #
    cP
    cz
    wcel
    #
    @15
    @17
    pgpfac1.u
    wph
    cP
    cprime
    wcel
    #
    @20
    wph
    cP
    cG
    cpgp
    wbr
    #
    @21
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
    @16
    cU
    c.x
    cG
    cP
    cC
    pgpfac1.mg
    subgmulgcl
    syl3anc
    #
    adantr
    wph
    @4
    simpr
    eldifd
    wph
    vw
    cA
    cB
    @0
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
    syldan
    eleqtrrd
    ex
    wph
    @13
    cC
    vs
    cv
    #
    vt
    cv
    #
    cG
    csg
    cfv
    #
    co
    #
    wceq
    #
    vt
    @11
    wrex
    #
    vs
    @1
    wrex
    cC
    @26
    @5
    @0
    c.x
    co
    #
    @28
    co
    #
    wceq
    #
    vk
    cz
    wrex
    #
    vs
    @1
    wrex
    #
    @10
    wph
    vs
    vt
    c.po
    @1
    @11
    cG
    @28
    cC
    @28
    eqid
    #
    pgpfac1.l
    wph
    cG
    cabl
    wcel
    #
    cS
    @18
    wcel
    cW
    @18
    wcel
    @1
    @18
    wcel
    #
    pgpfac1.g
    wph
    cS
    cA
    csn
    cK
    cfv
    #
    @18
    pgpfac1.s
    wph
    @18
    cB
    cmre
    cfv
    wcel
    #
    cA
    cB
    wcel
    @40
    @18
    wcel
    wph
    @18
    cB
    wph
    cG
    cgrp
    wcel
    #
    @18
    cB
    cacs
    cfv
    wcel
    wph
    @38
    @42
    pgpfac1.g
    cG
    ablgrp
    syl
    #
    cB
    cG
    pgpfac1.b
    subgacs
    syl
    acsmred
    #
    wph
    cU
    cB
    cA
    wph
    @19
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
    pgpfac1.au
    sseldd
    @18
    cA
    cK
    cB
    pgpfac1.k
    mrcsncl
    syl2anc
    syl5eqel
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
    @41
    @0
    cB
    wcel
    #
    @11
    @18
    wcel
    @44
    wph
    cU
    cB
    @0
    @45
    @25
    sseldd
    #
    @18
    @0
    cK
    cB
    pgpfac1.k
    mrcsncl
    syl2anc
    lsmelvalm
    wph
    @31
    @35
    vs
    @1
    wph
    @31
    @30
    vt
    vk
    cz
    @32
    cmpt
    #
    crn
    #
    wrex
    #
    @35
    wph
    @30
    vt
    @11
    @50
    wph
    @42
    @47
    @11
    @50
    wceq
    @43
    @48
    vk
    @0
    c.x
    @49
    cG
    cK
    cB
    pgpfac1.b
    pgpfac1.mg
    @49
    eqid
    #
    pgpfac1.k
    cycsubg2
    syl2anc
    rexeqdv
    @32
    cvv
    wcel
    #
    vk
    cz
    wral
    @51
    @35
    wb
    wph
    @53
    vk
    cz
    @5
    @0
    c.x
    ovex
    rgenw
    @30
    @34
    vk
    vt
    cz
    @32
    @49
    cvv
    @52
    @27
    @32
    wceq
    @29
    @33
    cC
    @27
    @32
    @26
    @28
    oveq2
    eqeq2d
    rexrnmpt
    mp1i
    bitrd
    rexbidv
    @36
    @34
    vs
    @1
    wrex
    #
    vk
    cz
    wrex
    wph
    @10
    @34
    vs
    vk
    @1
    cz
    rexcom
    wph
    @54
    @9
    vk
    cz
    wph
    @5
    cz
    wcel
    #
    wa
    #
    @54
    @26
    @8
    wceq
    #
    vs
    @1
    wrex
    @9
    @56
    @34
    @57
    vs
    @1
    @56
    @26
    @1
    wcel
    #
    wa
    #
    @33
    cC
    wceq
    #
    @8
    @26
    wceq
    #
    @34
    @57
    @59
    @60
    cC
    @32
    cG
    cplusg
    cfv
    #
    co
    #
    @26
    wceq
    #
    @61
    @59
    @42
    @26
    cB
    wcel
    @32
    cB
    wcel
    #
    cC
    cB
    wcel
    #
    @60
    @64
    wb
    wph
    @42
    @55
    @58
    @43
    ad2antrr
    #
    @56
    @1
    cB
    @26
    wph
    @1
    cB
    wss
    @55
    wph
    @1
    cU
    cB
    pgpfac1.ss
    @45
    sstrd
    adantr
    sselda
    @59
    @42
    @55
    @47
    @65
    @67
    wph
    @55
    @58
    simplr
    #
    wph
    @47
    @55
    @58
    @48
    ad2antrr
    cB
    c.x
    cG
    @5
    @0
    pgpfac1.b
    pgpfac1.mg
    mulgcl
    syl3anc
    wph
    @66
    @55
    @58
    wph
    cU
    cB
    cC
    @45
    @16
    sseldd
    #
    ad2antrr
    #
    cB
    @62
    cG
    @28
    @26
    @32
    cC
    pgpfac1.b
    @62
    eqid
    #
    @37
    grpsubadd
    syl13anc
    @59
    @8
    @63
    @26
    @59
    @8
    c1
    cC
    c.x
    co
    #
    @6
    cC
    c.x
    co
    #
    @62
    co
    #
    @63
    @59
    @42
    c1
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @66
    @8
    @74
    wceq
    @67
    @59
    1zzd
    @59
    @5
    cP
    @68
    wph
    @20
    @55
    @58
    @24
    ad2antrr
    #
    zmulcld
    @70
    cB
    @62
    c.x
    cG
    c1
    @6
    cC
    pgpfac1.b
    pgpfac1.mg
    @71
    mulgdir
    syl13anc
    @59
    @72
    cC
    @73
    @32
    @62
    @59
    @66
    @72
    cC
    wceq
    @70
    cB
    c.x
    cG
    cC
    pgpfac1.b
    pgpfac1.mg
    mulg1
    syl
    @59
    @42
    @55
    @20
    @66
    @73
    @32
    wceq
    @67
    @68
    @77
    @70
    cB
    c.x
    cG
    @5
    cP
    cC
    pgpfac1.b
    pgpfac1.mg
    mulgass
    syl13anc
    oveq12d
    eqtrd
    eqeq1d
    bitr4d
    cC
    @33
    eqcom
    @26
    @8
    eqcom
    3bitr4g
    rexbidva
    vs
    @8
    @1
    risset
    syl6bbr
    rexbidva
    syl5bb
    3bitrd
    sylibd
    wph
    @9
    @3
    vk
    cz
    @56
    va
    cv
    #
    @8
    c.x
    co
    #
    cC
    wceq
    #
    va
    cz
    wrex
    #
    @9
    @3
    wi
    #
    @56
    @42
    @66
    @7
    cz
    wcel
    #
    @7
    cC
    cO
    cfv
    #
    cgcd
    co
    c1
    wceq
    #
    @81
    wph
    @42
    @55
    @43
    adantr
    wph
    @66
    @55
    @69
    adantr
    #
    @56
    @75
    @76
    @83
    1z
    @55
    @55
    @20
    @76
    wph
    @55
    id
    @24
    @5
    cP
    zmulcl
    syl2anr
    c1
    @6
    zaddcl
    sylancr
    #
    @56
    @83
    @84
    cz
    wcel
    cB
    chash
    cfv
    #
    cz
    wcel
    #
    @7
    @88
    cgcd
    co
    #
    c1
    wceq
    @84
    @88
    cdvds
    wbr
    #
    @85
    @87
    @56
    @84
    @56
    @66
    @84
    cn0
    wcel
    @86
    cC
    cG
    cO
    cB
    pgpfac1.b
    pgpfac1.o
    odcl
    syl
    nn0zd
    wph
    @89
    @55
    wph
    @88
    wph
    cB
    cfn
    wcel
    #
    @88
    cn0
    wcel
    pgpfac1.n
    cB
    hashcl
    syl
    nn0zd
    adantr
    #
    @56
    @90
    @88
    @7
    cgcd
    co
    #
    cP
    cP
    @88
    cpc
    co
    #
    cexp
    co
    #
    @7
    cgcd
    co
    #
    c1
    @56
    @83
    @89
    @90
    @94
    wceq
    @87
    @93
    @7
    @88
    gcdcom
    syl2anc
    @56
    @88
    @96
    @7
    cgcd
    wph
    @88
    @96
    wceq
    #
    @55
    wph
    @22
    @92
    @98
    pgpfac1.p
    pgpfac1.n
    cP
    cG
    cB
    pgpfac1.b
    pgphash
    syl2anc
    adantr
    oveq1d
    @56
    cP
    @7
    cgcd
    co
    #
    c1
    wceq
    #
    @97
    c1
    wceq
    #
    @56
    cP
    c1
    cgcd
    co
    #
    @99
    c1
    @56
    @55
    @20
    @75
    @102
    @99
    wceq
    wph
    @55
    simpr
    wph
    @20
    @55
    @24
    adantr
    #
    @56
    1zzd
    @5
    cP
    c1
    gcdaddm
    syl3anc
    @56
    @20
    @102
    c1
    wceq
    @103
    cP
    gcd1
    syl
    eqtr3d
    @56
    @20
    @83
    @95
    cn0
    wcel
    #
    @100
    @101
    wi
    @103
    @87
    wph
    @104
    @55
    wph
    cP
    @88
    @23
    wph
    @88
    cn
    wcel
    #
    cB
    c0
    wne
    #
    wph
    @42
    @106
    @43
    cB
    cG
    pgpfac1.b
    grpbn0
    syl
    wph
    @92
    @105
    @106
    wb
    pgpfac1.n
    cB
    hashnncl
    syl
    mpbird
    pccld
    adantr
    cP
    @7
    @95
    rpexp1i
    syl3anc
    mpd
    3eqtrd
    wph
    @91
    @55
    wph
    @42
    @92
    @66
    @91
    @43
    pgpfac1.n
    @69
    cC
    cG
    cO
    cB
    pgpfac1.b
    pgpfac1.o
    oddvds2
    syl3anc
    adantr
    @7
    @84
    @88
    rpdvds
    syl32anc
    va
    cC
    c.x
    cG
    @7
    cO
    cB
    pgpfac1.b
    pgpfac1.o
    pgpfac1.mg
    odbezout
    syl31anc
    @56
    @80
    @82
    va
    cz
    @56
    @78
    cz
    wcel
    #
    wa
    #
    @9
    @79
    @1
    wcel
    #
    wi
    #
    @80
    @82
    @108
    @39
    @107
    @110
    wph
    @39
    @55
    @107
    @46
    ad2antrr
    @56
    @107
    simpr
    @39
    @107
    @9
    @109
    @1
    c.x
    cG
    @78
    @8
    pgpfac1.mg
    subgmulgcl
    3expia
    syl2anc
    @80
    @109
    @3
    @9
    @79
    cC
    @1
    eleq1
    imbi2d
    syl5ibcom
    rexlimdva
    mpd
    rexlimdva
    syld
    mt3d
end
