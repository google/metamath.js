include "cv.mm"
include "co.mm"
include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "cs3.mm"
include "ccgrg.mm"
include "chpg.mm"
include "wa.mm"
include "wrex.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "ad3antrrr.mm"
include "ad6antr.mm"
include "simprl.mm"
include "ad5antr.mm"
include "c2.mm"
include "cstrkgld.mm"
include "ncoltgdim2.mm"
include "ad4antr.mm"
include "crn.mm"
include "ncolne1.mm"
include "tgelrnln.mm"
include "simplr.mm"
include "tglnpt.mm"
include "wne.mm"
include "ad7antr.mm"
include "tglinecom.mm"
include "eleqtrd.mm"
include "simp-6r.mm"
include "perpln1.mm"
include "perpcom.mm"
include "wn.mm"
include "wo.mm"
include "ncolrot2.mm"
include "ioran.mm"
include "sylib.mm"
include "simpld.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "necomd.mm"
include "3brtr3d.mm"
include "perprag.mm"
include "tgcgrneq.mm"
include "neneqd.mm"
include "orcd.mm"
include "colrot2.mm"
include "colcom.mm"
include "simpr.mm"
include "lnxfr.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"
include "lncom.mm"
include "simprrr.mm"
include "eqcomd.mm"
include "simpllr.mm"
include "perpln2.mm"
include "tglnne.mm"
include "3brtr4d.mm"
include "simprrl.mm"
include "hlln.mm"
include "colperp.mm"
include "cgr3simp2.mm"
include "hypcgr.mm"
include "cmir.mm"
include "eqbrtrd.mm"
include "ragcom.mm"
include "eqbrtrrd.mm"
include "tgcgrcomlr.mm"
include "cgr3simp3.mm"
include "trgcgr.mm"
include "cdif.mm"
include "copab.mm"
include "simpl.mm"
include "eqidd.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "simpll.mm"
include "oveq12d.mm"
include "cbvrexdva.mm"
include "cbvopabv.mm"
include "ad8antr.mm"
include "colrot1.mm"
include "trgcgrcom.mm"
include "pm2.65da.mm"
include "jca.mm"
include "colhp.mm"
include "mpbird.mm"
include "simplrr.mm"
include "hpgtr.mm"
include "hlcgrex.mm"
include "reximddv.mm"
include "lnperpex.mm"
include "r19.29a.mm"
include "lnext.mm"
include "footex.mm"

theorem trgcopy
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vq: setvar q
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume trgcopy.p: |- P = ( Base ` G )
  assume trgcopy.m: |- .- = ( dist ` G )
  assume trgcopy.i: |- I = ( Itv ` G )
  assume trgcopy.l: |- L = ( LineG ` G )
  assume trgcopy.k: |- K = ( hlG ` G )
  assume trgcopy.g: |- ( ph -> G e. TarskiG )
  assume trgcopy.a: |- ( ph -> A e. P )
  assume trgcopy.b: |- ( ph -> B e. P )
  assume trgcopy.c: |- ( ph -> C e. P )
  assume trgcopy.d: |- ( ph -> D e. P )
  assume trgcopy.e: |- ( ph -> E e. P )
  assume trgcopy.f: |- ( ph -> F e. P )
  assume trgcopy.1: |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) )
  assume trgcopy.2: |- ( ph -> -. ( D e. ( E L F ) \/ E = F ) )
  assume trgcopy.3: |- ( ph -> ( A .- B ) = ( D .- E ) )

  disjoint .- f
  disjoint A f
  disjoint B f
  disjoint C f
  disjoint D f
  disjoint E f
  disjoint F f
  disjoint G f
  disjoint I f
  disjoint L f
  disjoint P f
  disjoint f ph
  disjoint K f
  disjoint .- a
  disjoint .- b
  disjoint .- j
  disjoint .- k
  disjoint .- l
  disjoint .- q
  disjoint .- t
  disjoint .- v
  disjoint .- w
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint a b
  disjoint a f
  disjoint a j
  disjoint a k
  disjoint a l
  disjoint a q
  disjoint a t
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b f
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b q
  disjoint b t
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f q
  disjoint f t
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint j k
  disjoint j l
  disjoint j q
  disjoint j t
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k l
  disjoint k q
  disjoint k t
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint l q
  disjoint l t
  disjoint l v
  disjoint l w
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint q t
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint A b
  disjoint A j
  disjoint A k
  disjoint A l
  disjoint A q
  disjoint A t
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B a
  disjoint B b
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B q
  disjoint B t
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C a
  disjoint C b
  disjoint C j
  disjoint C k
  disjoint C l
  disjoint C q
  disjoint C t
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D a
  disjoint D b
  disjoint D j
  disjoint D k
  disjoint D l
  disjoint D q
  disjoint D t
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E a
  disjoint E b
  disjoint E j
  disjoint E k
  disjoint E l
  disjoint E q
  disjoint E t
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint F a
  disjoint F b
  disjoint F j
  disjoint F k
  disjoint F l
  disjoint F q
  disjoint F t
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G a
  disjoint G b
  disjoint G j
  disjoint G k
  disjoint G l
  disjoint G q
  disjoint G t
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint I a
  disjoint I b
  disjoint I j
  disjoint I k
  disjoint I l
  disjoint I q
  disjoint I t
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint L a
  disjoint L b
  disjoint L j
  disjoint L k
  disjoint L l
  disjoint L q
  disjoint L t
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint P a
  disjoint P b
  disjoint P j
  disjoint P k
  disjoint P l
  disjoint P q
  disjoint P t
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint a ph
  disjoint b ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph q
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint K a
  disjoint K j
  disjoint K k
  disjoint K l
  assert |- ( ph -> E. f e. P ( <" A B C "> ( cgrG ` G ) <" D E f "> /\ f ( ( hpG ` G ) ` ( D L E ) ) F ) )

  proof
    wph
    cC
    vx
    cv
    #
    cL
    co
    #
    cA
    cB
    cL
    co
    #
    cG
    cperpg
    cfv
    #
    wbr
    #
    cA
    cB
    cC
    cs3
    cD
    cE
    vf
    cv
    #
    cs3
    cG
    ccgrg
    cfv
    #
    wbr
    #
    @5
    cF
    cD
    cE
    cL
    co
    #
    cG
    chpg
    cfv
    cfv
    #
    wbr
    #
    wa
    #
    vf
    cP
    wrex
    #
    vx
    @2
    wph
    @0
    @2
    wcel
    #
    wa
    #
    @4
    wa
    #
    cA
    cB
    @0
    cs3
    cD
    cE
    vy
    cv
    #
    cs3
    @6
    wbr
    #
    @12
    vy
    cP
    @15
    @16
    cP
    wcel
    #
    wa
    #
    @17
    wa
    #
    @8
    vq
    cv
    #
    @16
    cL
    co
    #
    @3
    wbr
    #
    @21
    cF
    @9
    wbr
    #
    wa
    #
    @12
    vq
    cP
    @20
    @21
    cP
    wcel
    #
    wa
    #
    @25
    wa
    #
    @5
    @21
    @16
    cK
    cfv
    wbr
    #
    @16
    @5
    c.mi
    co
    #
    @0
    cC
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @11
    vf
    cP
    @28
    @5
    cP
    wcel
    #
    @33
    wa
    #
    wa
    #
    @7
    @10
    @36
    cA
    cB
    cC
    cD
    cP
    @6
    cE
    @5
    cG
    c.mi
    trgcopy.p
    trgcopy.m
    @6
    eqid
    #
    @28
    cG
    cstrkg
    wcel
    #
    @35
    @20
    @38
    @26
    @25
    @15
    @38
    @18
    @17
    wph
    @38
    @13
    @4
    trgcopy.g
    ad2antrr
    #
    ad2antrr
    #
    ad2antrr
    #
    adantr
    #
    @20
    cA
    cP
    wcel
    #
    @26
    @25
    @35
    @15
    @43
    @18
    @17
    wph
    @43
    @13
    @4
    trgcopy.a
    ad2antrr
    #
    ad2antrr
    #
    ad3antrrr
    #
    @20
    cB
    cP
    wcel
    #
    @26
    @25
    @35
    @15
    @47
    @18
    @17
    wph
    @47
    @13
    @4
    trgcopy.b
    ad2antrr
    #
    ad2antrr
    #
    ad3antrrr
    #
    @28
    cC
    cP
    wcel
    #
    @35
    wph
    @51
    @13
    @4
    @18
    @17
    @26
    @25
    trgcopy.c
    ad6antr
    #
    adantr
    #
    @20
    cD
    cP
    wcel
    #
    @26
    @25
    @35
    @15
    @54
    @18
    @17
    wph
    @54
    @13
    @4
    trgcopy.d
    ad2antrr
    #
    ad2antrr
    #
    ad3antrrr
    #
    @20
    cE
    cP
    wcel
    #
    @26
    @25
    @35
    @15
    @58
    @18
    @17
    wph
    @58
    @13
    @4
    trgcopy.e
    ad2antrr
    #
    ad2antrr
    #
    ad3antrrr
    #
    @28
    @34
    @33
    simprl
    #
    @15
    cA
    cB
    c.mi
    co
    cD
    cE
    c.mi
    co
    wceq
    #
    @18
    @17
    @26
    @25
    @35
    wph
    @63
    @13
    @4
    trgcopy.3
    ad2antrr
    #
    ad5antr
    @36
    cB
    @0
    cC
    cE
    cP
    @16
    @5
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @42
    @20
    cG
    c2
    cstrkgld
    wbr
    #
    @26
    @25
    @35
    wph
    @65
    @13
    @4
    @18
    @17
    wph
    cP
    cG
    cI
    cL
    cB
    cC
    cA
    trgcopy.p
    trgcopy.l
    trgcopy.i
    trgcopy.g
    trgcopy.b
    trgcopy.c
    trgcopy.a
    trgcopy.1
    ncoltgdim2
    ad4antr
    #
    ad3antrrr
    #
    @50
    @28
    @0
    cP
    wcel
    #
    @35
    @20
    @68
    @26
    @25
    @15
    @68
    @18
    @17
    @15
    @2
    cP
    cG
    cI
    cL
    @0
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @39
    wph
    @2
    cL
    crn
    #
    wcel
    #
    @13
    @4
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    trgcopy.a
    trgcopy.b
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    trgcopy.a
    trgcopy.b
    trgcopy.c
    trgcopy.1
    ncolne1
    #
    tgelrnln
    #
    ad2antrr
    #
    wph
    @13
    @4
    simplr
    #
    tglnpt
    #
    ad2antrr
    #
    ad2antrr
    #
    adantr
    #
    @53
    @61
    @28
    @18
    @35
    @20
    @18
    @26
    @25
    @15
    @18
    @17
    simplr
    #
    ad2antrr
    #
    adantr
    #
    @62
    @36
    cB
    cA
    @0
    cC
    cP
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @42
    @50
    @46
    @36
    @0
    @2
    cB
    cA
    cL
    co
    #
    @15
    @13
    @18
    @17
    @26
    @25
    @35
    @74
    ad5antr
    #
    @36
    cP
    cA
    cB
    cG
    cI
    cL
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @46
    @50
    wph
    cA
    cB
    wne
    @13
    @4
    @18
    @17
    @26
    @25
    @35
    @71
    ad7antr
    tglinecom
    #
    eleqtrd
    @53
    @36
    @2
    @1
    @82
    @0
    cC
    cL
    co
    #
    @3
    @36
    @1
    @2
    cP
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @42
    @36
    @1
    @2
    cG
    cL
    trgcopy.l
    @42
    @14
    @4
    @18
    @17
    @26
    @25
    @35
    simp-6r
    #
    perpln1
    @15
    @70
    @18
    @17
    @26
    @25
    @35
    @73
    ad5antr
    @86
    perpcom
    @84
    @36
    cP
    cC
    @0
    cG
    cI
    cL
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @53
    @78
    @36
    @0
    cC
    @28
    @0
    cC
    wne
    #
    @35
    @15
    @87
    @18
    @17
    @26
    @25
    @15
    @13
    cC
    @2
    wcel
    #
    wn
    #
    @87
    @74
    wph
    @89
    @13
    @4
    wph
    @89
    cA
    cB
    wceq
    #
    wn
    #
    wph
    @88
    @90
    wo
    wn
    @89
    @91
    wa
    wph
    cP
    cG
    cI
    cL
    cB
    cC
    cA
    trgcopy.p
    trgcopy.l
    trgcopy.i
    trgcopy.g
    trgcopy.b
    trgcopy.c
    trgcopy.a
    trgcopy.1
    ncolrot2
    @88
    @90
    ioran
    sylib
    simpld
    #
    ad2antrr
    @0
    cC
    @2
    nelne2
    syl2anc
    ad4antr
    #
    adantr
    #
    necomd
    tglinecom
    3brtr3d
    #
    perprag
    @36
    cE
    cD
    @16
    @5
    cP
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @42
    @61
    @57
    @36
    cP
    cG
    cI
    cL
    cE
    cD
    @16
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @61
    @57
    @81
    wph
    cE
    cD
    wne
    #
    @13
    @4
    @18
    @17
    @26
    @25
    @35
    wph
    cD
    cE
    wph
    cA
    cB
    cD
    cE
    cP
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.g
    trgcopy.a
    trgcopy.b
    trgcopy.d
    trgcopy.e
    trgcopy.3
    @71
    tgcgrneq
    #
    necomd
    #
    ad7antr
    #
    @20
    @16
    @8
    wcel
    #
    @26
    @25
    @35
    @20
    cD
    cE
    wceq
    #
    wn
    #
    @100
    @20
    cD
    cE
    wph
    cD
    cE
    wne
    @13
    @4
    @18
    @17
    @97
    ad4antr
    neneqd
    @20
    @101
    @100
    @20
    @100
    @101
    @20
    cP
    cG
    cI
    cL
    cE
    cD
    @16
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @40
    @60
    @56
    @79
    @20
    cP
    cG
    cI
    cL
    cD
    @16
    cE
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @40
    @56
    @79
    @60
    @20
    cD
    cE
    @16
    cP
    @6
    cG
    cI
    cL
    cA
    cB
    @0
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @40
    @45
    @49
    @76
    @37
    @56
    @60
    @79
    @15
    cB
    cA
    @0
    cL
    co
    wcel
    cA
    @0
    wceq
    wo
    @18
    @17
    @15
    cP
    cG
    cI
    cL
    @0
    cA
    cB
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @39
    @75
    @44
    @48
    @15
    cP
    cG
    cI
    cL
    cA
    cB
    @0
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @39
    @44
    @48
    @75
    @15
    @13
    @90
    @74
    orcd
    colrot2
    colcom
    #
    ad2antrr
    @19
    @17
    simpr
    #
    lnxfr
    colrot2
    colcom
    orcomd
    ord
    mpd
    #
    ad3antrrr
    #
    lncom
    @62
    @36
    @16
    @5
    cL
    co
    #
    cE
    cD
    cL
    co
    #
    cP
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @42
    @36
    cP
    cG
    cI
    cL
    @16
    @5
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @81
    @62
    @36
    @0
    cC
    @16
    @5
    cP
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @42
    @78
    @53
    @81
    @62
    @36
    @30
    @31
    @28
    @34
    @29
    @32
    simprrr
    eqcomd
    #
    @94
    tgcgrneq
    #
    tgelrnln
    @36
    cP
    cG
    cI
    cL
    cE
    cD
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @61
    @57
    @99
    tgelrnln
    #
    @36
    @16
    @21
    @5
    @108
    cP
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @42
    @81
    @20
    @26
    @25
    @35
    simpllr
    #
    @62
    @36
    @108
    @16
    @21
    cL
    co
    #
    cP
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @42
    @111
    @36
    cP
    cG
    cI
    cL
    @16
    @21
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @81
    @112
    @36
    @21
    @16
    @28
    @21
    @16
    wne
    @35
    @28
    cP
    cG
    cI
    cL
    @21
    @16
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @41
    @20
    @26
    @25
    simplr
    #
    @80
    @28
    @8
    @22
    cG
    cL
    trgcopy.l
    @41
    @27
    @23
    @24
    simprl
    #
    perpln2
    tglnne
    #
    adantr
    necomd
    #
    tgelrnln
    #
    @36
    @8
    @22
    @108
    @113
    @3
    @28
    @23
    @35
    @115
    adantr
    @36
    cP
    cE
    cD
    cG
    cI
    cL
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @61
    @57
    @99
    tglinecom
    #
    @36
    cP
    @16
    @21
    cG
    cI
    cL
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @81
    @112
    @36
    cP
    cG
    cI
    cL
    @16
    @21
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @81
    @112
    @118
    tglnne
    tglinecom
    3brtr4d
    perpcom
    @36
    @5
    @113
    wcel
    @16
    @21
    wceq
    @36
    cP
    cG
    cI
    cL
    @16
    @21
    @5
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @81
    @112
    @62
    @117
    @36
    @5
    @21
    @16
    cP
    cG
    cI
    cK
    cL
    trgcopy.p
    trgcopy.i
    trgcopy.k
    @62
    @112
    @81
    @42
    trgcopy.l
    @28
    @34
    @29
    @32
    simprrl
    #
    hlln
    #
    lncom
    orcd
    @110
    colperp
    perpcom
    #
    perprag
    @36
    cA
    cB
    @0
    cD
    cP
    @6
    cE
    @16
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @37
    @42
    @46
    @50
    @78
    @57
    @61
    @81
    @20
    @17
    @26
    @25
    @35
    @104
    ad3antrrr
    #
    cgr3simp2
    @109
    hypcgr
    @36
    cC
    @0
    cA
    @5
    cP
    @16
    cD
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @42
    @67
    @53
    @78
    @46
    @62
    @81
    @57
    @36
    cA
    @0
    cC
    cP
    cG
    cmir
    cfv
    #
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @124
    eqid
    #
    @42
    @46
    @78
    @53
    @36
    cA
    cB
    @0
    cC
    cP
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @42
    @46
    @50
    @83
    @53
    @36
    @2
    @82
    @85
    @3
    @84
    @95
    eqbrtrd
    perprag
    ragcom
    @36
    cD
    @16
    @5
    cP
    @124
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @125
    @42
    @57
    @81
    @62
    @36
    cD
    cE
    @16
    @5
    cP
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @42
    @57
    @61
    @106
    @62
    @36
    @108
    @8
    @107
    @3
    @119
    @122
    eqbrtrrd
    perprag
    ragcom
    @36
    @0
    cC
    @16
    @5
    cP
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @42
    @78
    @53
    @81
    @62
    @109
    tgcgrcomlr
    @36
    cA
    cB
    @0
    cD
    cP
    @6
    cE
    @16
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @37
    @42
    @46
    @50
    @78
    @57
    @61
    @81
    @123
    cgr3simp3
    hypcgr
    trgcgr
    #
    @36
    vj
    @5
    @21
    cF
    @8
    cP
    cG
    cI
    cL
    vw
    cv
    #
    cP
    @8
    cdif
    #
    wcel
    #
    vv
    cv
    #
    @128
    wcel
    #
    wa
    #
    vz
    cv
    #
    @127
    @130
    cI
    co
    #
    wcel
    #
    vz
    @8
    wrex
    #
    wa
    #
    vw
    vv
    copab
    #
    vk
    vl
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @20
    @8
    @69
    wcel
    #
    @26
    @25
    @35
    wph
    @139
    @13
    @4
    @18
    @17
    wph
    cP
    cG
    cI
    cL
    cD
    cE
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    trgcopy.d
    trgcopy.e
    @97
    tgelrnln
    ad4antr
    #
    ad3antrrr
    #
    @62
    @137
    vk
    cv
    #
    @128
    wcel
    #
    vl
    cv
    #
    @128
    wcel
    #
    wa
    #
    vj
    cv
    #
    @142
    @144
    cI
    co
    #
    wcel
    #
    vj
    @8
    wrex
    #
    wa
    vw
    vv
    vk
    vl
    @127
    @142
    wceq
    #
    @130
    @144
    wceq
    #
    wa
    #
    @132
    @146
    @136
    @150
    @153
    @129
    @143
    @131
    @145
    @153
    @127
    @142
    @128
    @128
    @151
    @152
    simpl
    @153
    @128
    eqidd
    #
    eleq12d
    @153
    @130
    @144
    @128
    @128
    @151
    @152
    simpr
    @154
    eleq12d
    anbi12d
    @153
    @135
    @149
    vz
    vj
    @8
    @153
    @133
    @147
    wceq
    #
    wa
    #
    @133
    @147
    @134
    @148
    @153
    @155
    simpr
    @156
    @127
    @142
    @130
    @144
    cI
    @151
    @152
    @155
    simpll
    @151
    @152
    @155
    simplr
    oveq12d
    eleq12d
    cbvrexdva
    anbi12d
    cbvopabv
    #
    @112
    @36
    @5
    @21
    @9
    wbr
    @29
    @5
    @8
    wcel
    #
    wn
    #
    wa
    @36
    @29
    @159
    @120
    @36
    @158
    cA
    cB
    cC
    cL
    co
    wcel
    cB
    cC
    wceq
    wo
    #
    @36
    @158
    wa
    #
    cP
    cG
    cI
    cL
    cC
    cB
    cA
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @36
    @38
    @158
    @42
    adantr
    #
    @36
    @51
    @158
    @53
    adantr
    #
    @36
    @47
    @158
    @50
    adantr
    #
    @36
    @43
    @158
    @46
    adantr
    #
    @161
    cP
    cG
    cI
    cL
    cA
    cC
    cB
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @162
    @165
    @163
    @164
    @161
    cA
    cB
    cC
    cP
    @6
    cG
    cI
    cL
    cD
    cE
    @5
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @162
    @36
    @54
    @158
    @57
    adantr
    #
    @36
    @58
    @158
    @61
    adantr
    #
    @36
    @34
    @158
    @62
    adantr
    #
    @37
    @165
    @164
    @163
    @161
    cP
    cG
    cI
    cL
    cE
    cD
    @5
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @162
    @167
    @166
    @168
    @161
    @5
    @108
    wcel
    cE
    cD
    wceq
    @161
    cP
    cG
    cI
    cL
    cE
    cD
    @5
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @162
    @167
    @166
    @168
    wph
    @96
    @13
    @4
    @18
    @17
    @26
    @25
    @35
    @158
    @98
    ad8antr
    @36
    @158
    simpr
    lncom
    orcd
    colrot1
    @161
    cA
    cB
    cC
    cD
    cP
    @6
    cE
    @5
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @37
    @162
    @165
    @164
    @163
    @166
    @167
    @168
    @36
    @7
    @158
    @126
    adantr
    trgcgrcom
    lnxfr
    colrot1
    colcom
    wph
    @160
    wn
    @13
    @4
    @18
    @17
    @26
    @25
    @35
    @158
    trgcopy.1
    ad8antr
    pm2.65da
    jca
    @36
    vj
    @5
    @21
    @16
    @8
    cP
    cG
    cI
    cK
    cL
    @138
    vk
    vl
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @42
    @141
    @62
    @157
    @112
    @106
    @36
    cP
    cG
    cI
    cL
    @21
    @16
    @5
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @42
    @112
    @81
    @62
    @36
    @5
    @22
    wcel
    @21
    @16
    wceq
    @121
    orcd
    colrot2
    trgcopy.k
    colhp
    mpbird
    @28
    cF
    cP
    wcel
    #
    @35
    @20
    @169
    @26
    @25
    wph
    @169
    @13
    @4
    @18
    @17
    trgcopy.f
    ad4antr
    #
    ad2antrr
    adantr
    @27
    @23
    @24
    @35
    simplrr
    hpgtr
    jca
    @28
    vf
    @16
    @0
    cC
    @21
    cP
    cG
    cI
    cK
    c.mi
    trgcopy.p
    trgcopy.i
    trgcopy.k
    @80
    @77
    @52
    @41
    @114
    trgcopy.m
    @116
    @93
    hlcgrex
    reximddv
    @20
    vj
    @16
    @8
    cP
    cF
    cG
    cI
    cL
    c.mi
    @138
    vq
    vk
    vl
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @40
    @66
    @140
    @157
    @105
    @170
    wph
    cF
    @8
    wcel
    #
    wn
    #
    @13
    @4
    @18
    @17
    wph
    @172
    @102
    wph
    @171
    @101
    wo
    wn
    @172
    @102
    wa
    wph
    cP
    cG
    cI
    cL
    cE
    cF
    cD
    trgcopy.p
    trgcopy.l
    trgcopy.i
    trgcopy.g
    trgcopy.e
    trgcopy.f
    trgcopy.d
    trgcopy.2
    ncolrot2
    @171
    @101
    ioran
    sylib
    simpld
    ad4antr
    lnperpex
    r19.29a
    @15
    cD
    cE
    cP
    @6
    cG
    cI
    cL
    c.mi
    cA
    cB
    @0
    vy
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @39
    @44
    @48
    @75
    @37
    @55
    @59
    trgcopy.m
    @103
    @64
    lnext
    r19.29a
    wph
    vx
    @2
    cC
    cP
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    trgcopy.g
    @72
    trgcopy.c
    @92
    footex
    r19.29a
end
