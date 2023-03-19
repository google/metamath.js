include "cdvds.mm"
include "wbr.mm"
include "co.mm"
include "wcel.mm"
include "eldifbd.mm"
include "wn.mm"
include "c1o.mm"
include "cen.mm"
include "cpc.mm"
include "cexp.mm"
include "cc0.mm"
include "wceq.mm"
include "cprime.mm"
include "cn.mm"
include "wb.mm"
include "cpgp.mm"
include "pgpprm.mm"
include "syl.mm"
include "cgrp.mm"
include "cfn.mm"
include "cabl.mm"
include "ablgrp.mm"
include "gexcl2.mm"
include "syl2anc.mm"
include "pceq0.mm"
include "oveq2.mm"
include "syl6bir.mm"
include "c1.mm"
include "cv.mm"
include "cn0.mm"
include "wrex.mm"
include "chash.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "pccld.mm"
include "gexdvds3.mm"
include "pgphash.mm"
include "breqtrd.mm"
include "breq2d.mm"
include "rspcev.mm"
include "pcprmpw2.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "prmnn.mm"
include "nncnd.mm"
include "exp0d.mm"
include "eqeq12d.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "gex1.mm"
include "bitrd.mm"
include "sylibd.mm"
include "wa.mm"
include "csn.mm"
include "wss.mm"
include "csubg.mm"
include "cmre.mm"
include "cacs.mm"
include "subgacs.mm"
include "acsmred.mm"
include "subgss.mm"
include "sseldd.mm"
include "mrcsncl.mm"
include "syl5eqel.mm"
include "lsmsubg2.mm"
include "syl3anc.mm"
include "subg0cl.mm"
include "snssd.mm"
include "adantr.mm"
include "eldifad.mm"
include "grpidcl.mm"
include "en1eqsn.mm"
include "sylan.mm"
include "eleqtrd.mm"
include "ex.mm"
include "syld.mm"
include "mt3d.mm"
include "cdiv.mm"
include "cmul.mm"
include "nnne0d.mm"
include "divcan1d.mm"
include "eqtr4d.mm"
include "cin.mm"
include "cz.mm"
include "nndivdvds.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "mrcssidd.mm"
include "syl6sseqr.mm"
include "snssg.mm"
include "subgmulgcl.mm"
include "cplusg.mm"
include "prmz.mm"
include "mulgcl.mm"
include "eqid.mm"
include "mulgdi.mm"
include "syl13anc.mm"
include "oveq1d.mm"
include "mulgass.mm"
include "gexid.mm"
include "3eqtr3rd.mm"
include "oveq12d.mm"
include "grplid.mm"
include "3eqtr2d.mm"
include "eqeltrrd.mm"
include "elind.mm"
include "elsni.mm"
include "oddvds.mm"
include "eqbrtrrd.mm"
include "dvdscmulr.mm"
include "syl112anc.mm"
include "jca.mm"

theorem pgpfac1lem3a
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
  let cM: class M
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
  assume pgpfac1.m: |- ( ph -> M e. ZZ )
  assume pgpfac1.mw: |- ( ph -> ( ( P .x. C ) ( +g ` G ) ( M .x. A ) ) e. W )

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
  assert |- ( ph -> ( P || E /\ P || M ) )

  proof
    wph
    cP
    cE
    cdvds
    wbr
    #
    cP
    cM
    cdvds
    wbr
    #
    wph
    @0
    cC
    cS
    cW
    c.po
    co
    #
    wcel
    #
    wph
    cC
    cU
    @2
    pgpfac1.c
    eldifbd
    wph
    @0
    wn
    #
    cB
    c1o
    cen
    wbr
    #
    @3
    wph
    @4
    cP
    cP
    cE
    cpc
    co
    #
    cexp
    co
    #
    cP
    cc0
    cexp
    co
    #
    wceq
    #
    @5
    wph
    @4
    @6
    cc0
    wceq
    #
    @9
    wph
    cP
    cprime
    wcel
    #
    cE
    cn
    wcel
    #
    @10
    @4
    wb
    wph
    cP
    cG
    cpgp
    wbr
    #
    @11
    pgpfac1.p
    cP
    cG
    pgpprm
    syl
    #
    wph
    cG
    cgrp
    wcel
    #
    cB
    cfn
    wcel
    #
    @12
    wph
    cG
    cabl
    wcel
    #
    @15
    pgpfac1.g
    cG
    ablgrp
    syl
    #
    pgpfac1.n
    cE
    cG
    cB
    pgpfac1.b
    pgpfac1.e
    gexcl2
    syl2anc
    #
    cP
    cE
    pceq0
    syl2anc
    @6
    cc0
    cP
    cexp
    oveq2
    syl6bir
    wph
    @9
    cE
    c1
    wceq
    #
    @5
    wph
    @7
    cE
    @8
    c1
    wph
    cE
    @7
    wph
    cE
    cP
    vk
    cv
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    vk
    cn0
    wrex
    #
    cE
    @7
    wceq
    #
    wph
    cP
    cB
    chash
    cfv
    #
    cpc
    co
    #
    cn0
    wcel
    cE
    cP
    @27
    cexp
    co
    #
    cdvds
    wbr
    #
    @24
    wph
    cP
    @26
    @14
    wph
    @26
    cn
    wcel
    #
    cB
    c0
    wne
    #
    wph
    @15
    @31
    @18
    cB
    cG
    pgpfac1.b
    grpbn0
    syl
    wph
    @16
    @30
    @31
    wb
    pgpfac1.n
    cB
    hashnncl
    syl
    mpbird
    pccld
    wph
    cE
    @26
    @28
    cdvds
    wph
    @15
    @16
    cE
    @26
    cdvds
    wbr
    @18
    pgpfac1.n
    cE
    cG
    cB
    pgpfac1.b
    pgpfac1.e
    gexdvds3
    syl2anc
    wph
    @13
    @16
    @26
    @28
    wceq
    pgpfac1.p
    pgpfac1.n
    cP
    cG
    cB
    pgpfac1.b
    pgphash
    syl2anc
    breqtrd
    @23
    @29
    vk
    @27
    cn0
    @21
    @27
    wceq
    @22
    @28
    cE
    cdvds
    @21
    @27
    cP
    cexp
    oveq2
    breq2d
    rspcev
    syl2anc
    wph
    @11
    @12
    @24
    @25
    wb
    @14
    @19
    cE
    cP
    vk
    pcprmpw2
    syl2anc
    mpbid
    eqcomd
    wph
    cP
    wph
    cP
    wph
    @11
    cP
    cn
    wcel
    #
    @14
    cP
    prmnn
    syl
    #
    nncnd
    #
    exp0d
    eqeq12d
    wph
    cG
    cmnd
    wcel
    #
    @20
    @5
    wb
    wph
    @15
    @35
    @18
    cG
    grpmnd
    syl
    cE
    cG
    cB
    pgpfac1.b
    pgpfac1.e
    gex1
    syl
    bitrd
    sylibd
    wph
    @5
    @3
    wph
    @5
    wa
    #
    c.0
    csn
    #
    @2
    cC
    wph
    @37
    @2
    wss
    @5
    wph
    c.0
    @2
    wph
    @2
    cG
    csubg
    cfv
    #
    wcel
    #
    c.0
    @2
    wcel
    wph
    @17
    cS
    @38
    wcel
    #
    cW
    @38
    wcel
    #
    @39
    pgpfac1.g
    wph
    cS
    cA
    csn
    #
    cK
    cfv
    #
    @38
    pgpfac1.s
    wph
    @38
    cB
    cmre
    cfv
    wcel
    cA
    cB
    wcel
    #
    @43
    @38
    wcel
    wph
    @38
    cB
    wph
    @15
    @38
    cB
    cacs
    cfv
    wcel
    @18
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
    cU
    @38
    wcel
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
    #
    @38
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
    lsmsubg2
    syl3anc
    @2
    cG
    c.0
    pgpfac1.z
    subg0cl
    syl
    snssd
    adantr
    @36
    cC
    cB
    @37
    wph
    cC
    cB
    wcel
    #
    @5
    wph
    cU
    cB
    cC
    @46
    wph
    cC
    cU
    @2
    pgpfac1.c
    eldifad
    sseldd
    #
    adantr
    wph
    c.0
    cB
    wcel
    #
    @5
    cB
    @37
    wceq
    wph
    @15
    @51
    @18
    cB
    cG
    c.0
    pgpfac1.b
    pgpfac1.z
    grpidcl
    syl
    c.0
    cB
    en1eqsn
    sylan
    eleqtrd
    sseldd
    ex
    syld
    mt3d
    #
    wph
    cE
    cP
    cdiv
    co
    #
    cP
    cmul
    co
    #
    @53
    cM
    cmul
    co
    #
    cdvds
    wbr
    #
    @1
    wph
    cA
    cO
    cfv
    #
    @54
    @55
    cdvds
    wph
    @57
    cE
    @54
    pgpfac1.oe
    wph
    cE
    cP
    wph
    cE
    @19
    nncnd
    @34
    wph
    cP
    @33
    nnne0d
    divcan1d
    #
    eqtr4d
    wph
    @57
    @55
    cdvds
    wbr
    #
    @55
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    wph
    @60
    @37
    wcel
    @61
    wph
    @60
    cS
    cW
    cin
    @37
    wph
    cS
    cW
    @60
    wph
    @40
    @55
    cz
    wcel
    #
    cA
    cS
    wcel
    #
    @60
    cS
    wcel
    @48
    wph
    @53
    cM
    wph
    @53
    wph
    @0
    @53
    cn
    wcel
    #
    @52
    wph
    @12
    @32
    @0
    @64
    wb
    @19
    @33
    cE
    cP
    nndivdvds
    syl2anc
    mpbid
    #
    nnzd
    #
    pgpfac1.m
    zmulcld
    #
    wph
    @63
    @42
    cS
    wss
    #
    wph
    @42
    @43
    cS
    wph
    @38
    @42
    cK
    cB
    @45
    pgpfac1.k
    wph
    cA
    cB
    @47
    snssd
    mrcssidd
    pgpfac1.s
    syl6sseqr
    wph
    cA
    cU
    wcel
    @63
    @68
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
    @55
    cA
    pgpfac1.mg
    subgmulgcl
    syl3anc
    #
    wph
    @53
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
    cG
    cplusg
    cfv
    #
    co
    #
    c.x
    co
    #
    @60
    cW
    wph
    @74
    @53
    @70
    c.x
    co
    #
    @53
    @71
    c.x
    co
    #
    @72
    co
    #
    c.0
    @60
    @72
    co
    #
    @60
    wph
    @17
    @53
    cz
    wcel
    #
    @70
    cB
    wcel
    #
    @71
    cB
    wcel
    #
    @74
    @77
    wceq
    pgpfac1.g
    @66
    wph
    @15
    cP
    cz
    wcel
    #
    @49
    @80
    @18
    wph
    @11
    @82
    @14
    cP
    prmz
    syl
    #
    @50
    cB
    c.x
    cG
    cP
    cC
    pgpfac1.b
    pgpfac1.mg
    mulgcl
    syl3anc
    wph
    @15
    cM
    cz
    wcel
    #
    @44
    @81
    @18
    pgpfac1.m
    @47
    cB
    c.x
    cG
    cM
    cA
    pgpfac1.b
    pgpfac1.mg
    mulgcl
    syl3anc
    cB
    @72
    c.x
    cG
    @53
    @70
    @71
    pgpfac1.b
    pgpfac1.mg
    @72
    eqid
    #
    mulgdi
    syl13anc
    wph
    c.0
    @75
    @60
    @76
    @72
    wph
    @54
    cC
    c.x
    co
    #
    cE
    cC
    c.x
    co
    #
    @75
    c.0
    wph
    @54
    cE
    cC
    c.x
    @58
    oveq1d
    wph
    @15
    @79
    @82
    @49
    @86
    @75
    wceq
    @18
    @66
    @83
    @50
    cB
    c.x
    cG
    @53
    cP
    cC
    pgpfac1.b
    pgpfac1.mg
    mulgass
    syl13anc
    wph
    @49
    @87
    c.0
    wceq
    @50
    cC
    c.x
    cE
    cG
    cB
    c.0
    pgpfac1.b
    pgpfac1.e
    pgpfac1.mg
    pgpfac1.z
    gexid
    syl
    3eqtr3rd
    wph
    @15
    @79
    @84
    @44
    @60
    @76
    wceq
    @18
    @66
    pgpfac1.m
    @47
    cB
    c.x
    cG
    @53
    cM
    cA
    pgpfac1.b
    pgpfac1.mg
    mulgass
    syl13anc
    oveq12d
    wph
    @15
    @60
    cB
    wcel
    @78
    @60
    wceq
    @18
    wph
    cS
    cB
    @60
    wph
    @40
    cS
    cB
    wss
    @48
    cB
    cS
    cG
    pgpfac1.b
    subgss
    syl
    @69
    sseldd
    cB
    @72
    cG
    @60
    c.0
    pgpfac1.b
    @85
    pgpfac1.z
    grplid
    syl2anc
    3eqtr2d
    wph
    @41
    @79
    @73
    cW
    wcel
    @74
    cW
    wcel
    pgpfac1.w
    @66
    pgpfac1.mw
    cW
    c.x
    cG
    @53
    @73
    pgpfac1.mg
    subgmulgcl
    syl3anc
    eqeltrrd
    elind
    pgpfac1.i
    eleqtrd
    @60
    c.0
    elsni
    syl
    wph
    @15
    @44
    @62
    @59
    @61
    wb
    @18
    @47
    @67
    cA
    c.x
    cG
    @55
    cO
    cB
    c.0
    pgpfac1.b
    pgpfac1.o
    pgpfac1.mg
    pgpfac1.z
    oddvds
    syl3anc
    mpbird
    eqbrtrrd
    wph
    @82
    @84
    @79
    @53
    cc0
    wne
    @56
    @1
    wb
    @83
    pgpfac1.m
    @66
    wph
    @53
    @65
    nnne0d
    @53
    cP
    cM
    dvdscmulr
    syl112anc
    mpbid
    jca
end
