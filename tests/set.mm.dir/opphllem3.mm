include "cv.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "wceq.mm"
include "ad4antr.mm"
include "tglnpt.mm"
include "cstrkg.mm"
include "simplr.mm"
include "simprl.mm"
include "wne.mm"
include "perpln2.mm"
include "tglnne.mm"
include "simprr.mm"
include "tgcgrcomlr.mm"
include "cperpg.mm"
include "tgcgrneq.mm"
include "hlbtwn.mm"
include "cmir.mm"
include "eqid.mm"
include "adantr.mm"
include "ad5antr.mm"
include "simpr.mm"
include "mirhl.mm"
include "eqidd.mm"
include "fveq2d.mm"
include "ad2antrr.mm"
include "ad6antr.mm"
include "eqcomd.mm"
include "fveq1i.mm"
include "mircom.mm"
include "syl5eqr.mm"
include "miduniq.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "eqtr2d.mm"
include "necomd.mm"
include "crn.mm"
include "simp-4r.mm"
include "tglinethru.mm"
include "eqbrtrrd.mm"
include "tglinecom.mm"
include "3brtr3d.mm"
include "eleqtrd.mm"
include "simpllr.mm"
include "opphllem.mm"
include "r19.29a.mm"
include "breq123d.mm"
include "mpbid.mm"
include "mircl.mm"
include "mirmir.mm"
include "impbida.mm"
include "bitrd.mm"
include "wrex.mm"
include "cleg.mm"
include "legov.mm"
include "wn.mm"
include "islnopp.mm"
include "simprd.mm"

theorem opphllem3
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cV: class V
  assume hpg.p: |- P = ( Base ` G )
  assume hpg.d: |- .- = ( dist ` G )
  assume hpg.i: |- I = ( Itv ` G )
  assume hpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume opphl.l: |- L = ( LineG ` G )
  assume opphl.d: |- ( ph -> D e. ran L )
  assume opphl.g: |- ( ph -> G e. TarskiG )
  assume opphl.k: |- K = ( hlG ` G )
  assume opphllem5.n: |- N = ( ( pInvG ` G ) ` M )
  assume opphllem5.a: |- ( ph -> A e. P )
  assume opphllem5.c: |- ( ph -> C e. P )
  assume opphllem5.r: |- ( ph -> R e. D )
  assume opphllem5.s: |- ( ph -> S e. D )
  assume opphllem5.m: |- ( ph -> M e. P )
  assume opphllem5.o: |- ( ph -> A O C )
  assume opphllem5.p: |- ( ph -> D ( perpG ` G ) ( A L R ) )
  assume opphllem5.q: |- ( ph -> D ( perpG ` G ) ( C L S ) )
  assume opphllem3.t: |- ( ph -> R =/= S )
  assume opphllem3.l: |- ( ph -> ( S .- C ) ( leG ` G ) ( R .- A ) )
  assume opphllem3.u: |- ( ph -> U e. P )
  assume opphllem3.v: |- ( ph -> ( N ` R ) = S )

  disjoint D a
  disjoint D b
  disjoint a b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint P b
  disjoint A t
  disjoint D t
  disjoint R t
  disjoint C t
  disjoint G t
  disjoint L t
  disjoint U t
  disjoint I t
  disjoint K t
  disjoint M t
  disjoint O t
  disjoint N t
  disjoint P t
  disjoint S t
  disjoint ph t
  disjoint .- t
  disjoint a t
  disjoint b t
  disjoint A m
  disjoint A p
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint m p
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B m
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D m
  disjoint D p
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R m
  disjoint R p
  disjoint C m
  disjoint C p
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint G m
  disjoint G p
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint L m
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint U m
  disjoint U p
  disjoint I m
  disjoint I p
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint K p
  disjoint O m
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint N m
  disjoint N p
  disjoint P m
  disjoint P p
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S m
  disjoint S p
  disjoint V m
  disjoint V t
  disjoint m ph
  disjoint p ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .- m
  disjoint .- p
  disjoint .- x
  disjoint .- y
  disjoint .- z
  assert |- ( ph -> ( U ( K ` R ) A <-> ( N ` U ) ( K ` S ) C ) )

  proof
    wph
    vt
    cv
    #
    cA
    cC
    cI
    co
    wcel
    #
    cU
    cA
    cR
    cK
    cfv
    #
    wbr
    #
    cU
    cN
    cfv
    #
    cC
    cS
    cK
    cfv
    #
    wbr
    #
    wb
    #
    vt
    cD
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @1
    wa
    #
    vp
    cv
    #
    cR
    cA
    cI
    co
    wcel
    #
    cS
    cC
    c.mi
    co
    #
    cR
    @11
    c.mi
    co
    wceq
    #
    wa
    #
    @7
    vp
    cP
    @10
    @11
    cP
    wcel
    #
    wa
    #
    @15
    wa
    #
    @3
    cU
    @11
    @2
    wbr
    #
    @6
    @18
    cU
    cA
    cR
    @11
    cP
    cG
    cI
    cK
    hpg.p
    hpg.i
    opphl.k
    wph
    cU
    cP
    wcel
    #
    @8
    @1
    @16
    @15
    opphllem3.u
    ad4antr
    #
    wph
    cA
    cP
    wcel
    @8
    @1
    @16
    @15
    opphllem5.a
    ad4antr
    #
    wph
    cR
    cP
    wcel
    #
    @8
    @1
    @16
    @15
    wph
    cD
    cP
    cG
    cI
    cL
    cR
    hpg.p
    opphl.l
    hpg.i
    opphl.g
    opphl.d
    opphllem5.r
    tglnpt
    #
    ad4antr
    #
    wph
    cG
    cstrkg
    wcel
    #
    @8
    @1
    @16
    @15
    opphl.g
    ad4antr
    #
    @10
    @16
    @15
    simplr
    #
    @17
    @12
    @14
    simprl
    #
    wph
    cA
    cR
    wne
    @8
    @1
    @16
    @15
    wph
    cP
    cG
    cI
    cL
    cA
    cR
    hpg.p
    hpg.i
    opphl.l
    opphl.g
    opphllem5.a
    @24
    wph
    cD
    cA
    cR
    cL
    co
    #
    cG
    cL
    opphl.l
    opphl.g
    opphllem5.p
    perpln2
    tglnne
    ad4antr
    @18
    cC
    cS
    @11
    cR
    cP
    cG
    cI
    c.mi
    hpg.p
    hpg.d
    hpg.i
    @27
    wph
    cC
    cP
    wcel
    #
    @8
    @1
    @16
    @15
    opphllem5.c
    ad4antr
    #
    wph
    cS
    cP
    wcel
    #
    @8
    @1
    @16
    @15
    wph
    cD
    cP
    cG
    cI
    cL
    cS
    hpg.p
    opphl.l
    hpg.i
    opphl.g
    opphl.d
    opphllem5.s
    tglnpt
    #
    ad4antr
    #
    @28
    @25
    @18
    cS
    cC
    cR
    @11
    cP
    cG
    cI
    c.mi
    hpg.p
    hpg.d
    hpg.i
    @27
    @35
    @32
    @25
    @28
    @17
    @12
    @14
    simprr
    #
    tgcgrcomlr
    @18
    cP
    cG
    cI
    cL
    cC
    cS
    hpg.p
    hpg.i
    opphl.l
    @27
    @32
    @35
    @18
    cD
    cC
    cS
    cL
    co
    #
    cG
    cL
    opphl.l
    @27
    wph
    cD
    @37
    cG
    cperpg
    cfv
    #
    wbr
    @8
    @1
    @16
    @15
    opphllem5.q
    ad4antr
    #
    perpln2
    tglnne
    #
    tgcgrneq
    hlbtwn
    @18
    @19
    @6
    @18
    @19
    wa
    #
    @4
    @11
    cN
    cfv
    #
    cR
    cN
    cfv
    #
    cK
    cfv
    #
    wbr
    @6
    @41
    cM
    cP
    cG
    cmir
    cfv
    #
    cG
    cI
    cK
    cL
    cN
    c.mi
    cU
    @11
    cR
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @45
    eqid
    #
    @18
    @26
    @19
    @27
    adantr
    opphllem5.n
    opphl.k
    wph
    cM
    cP
    wcel
    #
    @8
    @1
    @16
    @15
    @19
    opphllem5.m
    ad5antr
    @18
    @20
    @19
    @21
    adantr
    @18
    @16
    @19
    @28
    adantr
    @18
    @23
    @19
    @25
    adantr
    @18
    @19
    simpr
    mirhl
    @41
    @4
    @4
    @42
    cC
    @44
    @5
    @41
    @4
    eqidd
    @41
    @43
    cS
    cK
    wph
    @43
    cS
    wceq
    #
    @8
    @1
    @16
    @15
    @19
    opphllem3.v
    ad5antr
    fveq2d
    @18
    @42
    cC
    wceq
    #
    @19
    @18
    cR
    cS
    vm
    cv
    #
    @45
    cfv
    #
    cfv
    #
    wceq
    #
    cC
    @11
    @51
    cfv
    #
    wceq
    #
    wa
    #
    @49
    vm
    cP
    @18
    @50
    cP
    wcel
    #
    wa
    #
    @56
    wa
    #
    cC
    @54
    @42
    @58
    @53
    @55
    simprr
    @59
    @11
    @51
    cN
    @59
    @51
    cM
    @45
    cfv
    #
    cN
    @59
    @50
    cM
    @45
    @59
    @50
    cM
    cP
    @45
    cG
    cI
    cL
    c.mi
    cS
    cR
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @46
    @18
    @26
    @57
    @56
    @27
    ad2antrr
    @18
    @57
    @56
    simplr
    wph
    @47
    @8
    @1
    @16
    @15
    @57
    @56
    opphllem5.m
    ad6antr
    @18
    @33
    @57
    @56
    @35
    ad2antrr
    @18
    @23
    @57
    @56
    @25
    ad2antrr
    @59
    cR
    @52
    @58
    @53
    @55
    simprl
    eqcomd
    wph
    cS
    @60
    cfv
    #
    cR
    wceq
    @8
    @1
    @16
    @15
    @57
    @56
    wph
    @61
    cS
    cN
    cfv
    #
    cR
    cS
    cN
    @60
    opphllem5.n
    fveq1i
    wph
    cM
    cR
    cS
    cP
    @45
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @46
    opphl.g
    opphllem5.m
    opphllem5.n
    @24
    opphllem3.v
    mircom
    syl5eqr
    ad6antr
    miduniq
    fveq2d
    opphllem5.n
    syl6eqr
    fveq1d
    eqtr2d
    @18
    vm
    cS
    cR
    cP
    cA
    @11
    @45
    @0
    cG
    cI
    cL
    c.mi
    cC
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @27
    @46
    @35
    @25
    @18
    cR
    cS
    wph
    cR
    cS
    wne
    @8
    @1
    @16
    @15
    opphllem3.t
    ad4antr
    necomd
    #
    @22
    @32
    @18
    cD
    cP
    cG
    cI
    cL
    @0
    hpg.p
    opphl.l
    hpg.i
    @27
    wph
    cD
    cL
    crn
    wcel
    @8
    @1
    @16
    @15
    opphl.d
    ad4antr
    #
    wph
    @8
    @1
    @16
    @15
    simp-4r
    #
    tglnpt
    @18
    cD
    cS
    cR
    cL
    co
    #
    @30
    @38
    @18
    cD
    cP
    cS
    cR
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    @27
    @35
    @25
    @63
    @63
    @64
    wph
    cS
    cD
    wcel
    @8
    @1
    @16
    @15
    opphllem5.s
    ad4antr
    wph
    cR
    cD
    wcel
    @8
    @1
    @16
    @15
    opphllem5.r
    ad4antr
    tglinethru
    #
    wph
    cD
    @30
    @38
    wbr
    @8
    @1
    @16
    @15
    opphllem5.p
    ad4antr
    eqbrtrrd
    @18
    cD
    @37
    @66
    cS
    cC
    cL
    co
    @38
    @39
    @67
    @18
    cP
    cC
    cS
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    @27
    @32
    @35
    @40
    tglinecom
    3brtr3d
    @18
    @0
    cD
    @66
    @65
    @67
    eleqtrd
    @9
    @1
    @16
    @15
    simpllr
    @28
    @29
    @36
    opphllem
    r19.29a
    #
    adantr
    breq123d
    mpbid
    @18
    @6
    wa
    #
    @4
    cN
    cfv
    #
    cC
    cN
    cfv
    #
    @62
    cK
    cfv
    #
    wbr
    @19
    @69
    cM
    cP
    @45
    cG
    cI
    cK
    cL
    cN
    c.mi
    @4
    cC
    cS
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @46
    @18
    @26
    @6
    @27
    adantr
    #
    opphllem5.n
    opphl.k
    wph
    @47
    @8
    @1
    @16
    @15
    @6
    opphllem5.m
    ad5antr
    #
    wph
    @4
    cP
    wcel
    @8
    @1
    @16
    @15
    @6
    wph
    cM
    cP
    @45
    cG
    cI
    cL
    cN
    c.mi
    cU
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @46
    opphl.g
    opphllem5.m
    opphllem5.n
    opphllem3.u
    mircl
    ad5antr
    @18
    @31
    @6
    @32
    adantr
    @18
    @33
    @6
    @35
    adantr
    @18
    @6
    simpr
    mirhl
    @69
    @70
    cU
    @71
    @11
    @72
    @2
    @69
    cM
    cU
    cP
    @45
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @46
    @73
    @74
    opphllem5.n
    @18
    @20
    @6
    @21
    adantr
    mirmir
    @69
    @62
    cR
    cK
    @69
    cM
    cR
    cS
    cP
    @45
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @46
    @73
    @74
    opphllem5.n
    @18
    @23
    @6
    @25
    adantr
    wph
    @48
    @8
    @1
    @16
    @15
    @6
    opphllem3.v
    ad5antr
    mircom
    fveq2d
    @69
    cM
    @11
    cC
    cP
    @45
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @46
    @73
    @74
    opphllem5.n
    @18
    @16
    @6
    @28
    adantr
    @18
    @49
    @6
    @68
    adantr
    mircom
    breq123d
    mpbid
    impbida
    bitrd
    wph
    @15
    vp
    cP
    wrex
    #
    @8
    @1
    wph
    @13
    cR
    cA
    c.mi
    co
    cG
    cleg
    cfv
    #
    wbr
    @75
    opphllem3.l
    wph
    vp
    cS
    cC
    cR
    cA
    cP
    cG
    cI
    @76
    c.mi
    hpg.p
    hpg.d
    hpg.i
    @76
    eqid
    opphl.g
    @34
    opphllem5.c
    @24
    opphllem5.a
    legov
    mpbid
    ad2antrr
    r19.29a
    wph
    cA
    cD
    wcel
    wn
    cC
    cD
    wcel
    wn
    wa
    #
    @1
    vt
    cD
    wrex
    #
    wph
    cA
    cC
    cO
    wbr
    @77
    @78
    wa
    opphllem5.o
    wph
    vt
    cA
    cC
    cD
    cP
    cG
    cI
    c.mi
    cO
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphllem5.a
    opphllem5.c
    islnopp
    mpbid
    simprd
    r19.29a
end
