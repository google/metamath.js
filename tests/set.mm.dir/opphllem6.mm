include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "wceq.mm"
include "wa.mm"
include "cmir.mm"
include "eqid.mm"
include "cstrkg.mm"
include "wcel.mm"
include "adantr.mm"
include "wne.mm"
include "tglnpt.mm"
include "co.mm"
include "perpln2.mm"
include "tglnne.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "mirinv.mm"
include "mpbid.mm"
include "neeqtrrd.mm"
include "eqtrd.mm"
include "cv.mm"
include "ad3antrrr.mm"
include "crn.mm"
include "simplr.mm"
include "simpllr.mm"
include "tglinerflx2.mm"
include "eqeltrd.mm"
include "cperpg.mm"
include "tgelrnln.mm"
include "perpcom.mm"
include "ad4antr.mm"
include "tglinethru.mm"
include "breqtrd.mm"
include "perprag.mm"
include "tgbtwncom.mm"
include "ragflat2.mm"
include "pm2.61dane.mm"
include "wrex.mm"
include "wn.mm"
include "islnopp.mm"
include "simprd.mm"
include "r19.29a.mm"
include "mirbtwnhl.mm"
include "fveq2d.mm"
include "breqd.mm"
include "3bitr3d.mm"
include "cleg.mm"
include "ad2antrr.mm"
include "opphllem3.mm"
include "oppcom.mm"
include "necomd.mm"
include "mircl.mm"
include "mircom.mm"
include "mirmir.mm"
include "breq1d.mm"
include "bitr2d.mm"
include "wo.mm"
include "legtrid.mm"
include "mpjaodan.mm"

theorem opphllem6
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
  assume opphllem5.u: |- ( ph -> U e. P )
  assume opphllem6.v: |- ( ph -> ( N ` R ) = S )

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
    cR
    cS
    wph
    cR
    cS
    wceq
    #
    wa
    #
    cU
    cA
    cM
    cK
    cfv
    #
    wbr
    @2
    cC
    @8
    wbr
    @1
    @4
    @7
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
    cA
    cC
    cU
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @9
    eqid
    #
    wph
    cG
    cstrkg
    wcel
    #
    @6
    opphl.g
    adantr
    opphllem5.n
    opphl.k
    wph
    cM
    cP
    wcel
    #
    @6
    opphllem5.m
    adantr
    wph
    cA
    cP
    wcel
    #
    @6
    opphllem5.a
    adantr
    wph
    cC
    cP
    wcel
    #
    @6
    opphllem5.c
    adantr
    wph
    cU
    cP
    wcel
    #
    @6
    opphllem5.u
    adantr
    @7
    cA
    cR
    cM
    wph
    cA
    cR
    wne
    @6
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
    #
    adantr
    @7
    cR
    cN
    cfv
    #
    cR
    wceq
    #
    cM
    cR
    wceq
    #
    @7
    @19
    cS
    cR
    wph
    @19
    cS
    wceq
    #
    @6
    opphllem6.v
    adantr
    wph
    @6
    simpr
    #
    eqtr4d
    wph
    @20
    @21
    wb
    @6
    wph
    cM
    cR
    cP
    @9
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @10
    opphl.g
    opphllem5.m
    opphllem5.n
    @16
    mirinv
    adantr
    mpbid
    #
    neeqtrrd
    @7
    cC
    cS
    cM
    wph
    cC
    cS
    wne
    @6
    wph
    cP
    cG
    cI
    cL
    cC
    cS
    hpg.p
    hpg.i
    opphl.l
    opphl.g
    opphllem5.c
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
    wph
    cD
    cC
    cS
    cL
    co
    #
    cG
    cL
    opphl.l
    opphl.g
    opphllem5.q
    perpln2
    tglnne
    #
    adantr
    @7
    cM
    cR
    cS
    @24
    @23
    eqtrd
    #
    neeqtrrd
    @7
    cM
    cR
    cA
    cC
    cI
    co
    #
    @24
    @7
    vt
    cv
    #
    @29
    wcel
    #
    cR
    @29
    wcel
    vt
    cD
    @7
    @30
    cD
    wcel
    #
    wa
    #
    @31
    wa
    #
    cR
    @30
    @29
    @34
    cR
    @30
    wceq
    #
    cR
    @30
    @34
    @35
    simpr
    @34
    cR
    @30
    wne
    #
    wa
    #
    cC
    cR
    @30
    cA
    cP
    @9
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @10
    @34
    @11
    @36
    wph
    @11
    @6
    @32
    @31
    opphl.g
    ad3antrrr
    #
    adantr
    #
    @34
    @14
    @36
    wph
    @14
    @6
    @32
    @31
    opphllem5.c
    ad3antrrr
    adantr
    #
    @34
    cR
    cP
    wcel
    #
    @36
    wph
    @41
    @6
    @32
    @31
    @16
    ad3antrrr
    adantr
    #
    @34
    @30
    cP
    wcel
    @36
    @34
    cD
    cP
    cG
    cI
    cL
    @30
    hpg.p
    opphl.l
    hpg.i
    @38
    wph
    cD
    cL
    crn
    wcel
    #
    @6
    @32
    @31
    opphl.d
    ad3antrrr
    #
    @7
    @32
    @31
    simplr
    #
    tglnpt
    adantr
    #
    @34
    @13
    @36
    wph
    @13
    @6
    @32
    @31
    opphllem5.a
    ad3antrrr
    adantr
    #
    @37
    cC
    cS
    cR
    @30
    cP
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @39
    @40
    @34
    cS
    cP
    wcel
    #
    @36
    wph
    @48
    @6
    @32
    @31
    @25
    ad3antrrr
    adantr
    @34
    cR
    @26
    wcel
    @36
    @34
    cR
    cS
    @26
    wph
    @6
    @32
    @31
    simpllr
    wph
    cS
    @26
    wcel
    @6
    @32
    @31
    wph
    cP
    cC
    cS
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    opphl.g
    opphllem5.c
    @25
    @27
    tglinerflx2
    ad3antrrr
    eqeltrd
    adantr
    @46
    @37
    @26
    cD
    cR
    @30
    cL
    co
    #
    cG
    cperpg
    cfv
    #
    wph
    @26
    cD
    @50
    wbr
    @6
    @32
    @31
    @36
    wph
    cD
    @26
    cP
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    opphl.g
    opphl.d
    wph
    cP
    cG
    cI
    cL
    cC
    cS
    hpg.p
    hpg.i
    opphl.l
    opphl.g
    opphllem5.c
    @25
    @27
    tgelrnln
    opphllem5.q
    perpcom
    ad4antr
    @37
    cD
    cP
    cR
    @30
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    @39
    @42
    @46
    @34
    @36
    simpr
    #
    @51
    @34
    @43
    @36
    @44
    adantr
    @34
    cR
    cD
    wcel
    #
    @36
    wph
    @52
    @6
    @32
    @31
    opphllem5.r
    ad3antrrr
    adantr
    @34
    @32
    @36
    @45
    adantr
    tglinethru
    #
    breqtrd
    perprag
    @37
    cA
    cR
    cR
    @30
    cP
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @39
    @47
    @42
    @34
    cR
    @17
    wcel
    #
    @36
    wph
    @54
    @6
    @32
    @31
    wph
    cP
    cA
    cR
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    opphl.g
    opphllem5.a
    @16
    @18
    tglinerflx2
    ad3antrrr
    adantr
    @46
    @37
    @17
    cD
    @49
    @50
    wph
    @17
    cD
    @50
    wbr
    @6
    @32
    @31
    @36
    wph
    cD
    @17
    cP
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    opphl.g
    opphl.d
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
    @16
    @18
    tgelrnln
    opphllem5.p
    perpcom
    ad4antr
    @53
    breqtrd
    perprag
    @37
    cA
    @30
    cC
    cP
    cG
    cI
    c.mi
    hpg.p
    hpg.d
    hpg.i
    @39
    @47
    @46
    @40
    @33
    @31
    @36
    simplr
    tgbtwncom
    ragflat2
    pm2.61dane
    @33
    @31
    simpr
    eqeltrd
    wph
    @31
    vt
    cD
    wrex
    #
    @6
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
    @55
    wph
    cA
    cC
    cO
    wbr
    #
    @56
    @55
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
    adantr
    r19.29a
    eqeltrd
    mirbtwnhl
    @7
    @8
    @0
    cU
    cA
    @7
    cM
    cR
    cK
    @24
    fveq2d
    breqd
    @7
    @8
    @3
    @2
    cC
    @7
    cM
    cS
    cK
    @28
    fveq2d
    breqd
    3bitr3d
    wph
    cR
    cS
    wne
    #
    wa
    #
    cS
    cC
    c.mi
    co
    #
    cR
    cA
    c.mi
    co
    #
    cG
    cleg
    cfv
    #
    wbr
    #
    @5
    @61
    @60
    @62
    wbr
    #
    @59
    @63
    wa
    vt
    cA
    cC
    cD
    cP
    cR
    cS
    cU
    cG
    cI
    cK
    cL
    cM
    c.mi
    cN
    cO
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    wph
    @43
    @58
    @63
    opphl.d
    ad2antrr
    wph
    @11
    @58
    @63
    opphl.g
    ad2antrr
    opphl.k
    opphllem5.n
    wph
    @13
    @58
    @63
    opphllem5.a
    ad2antrr
    wph
    @14
    @58
    @63
    opphllem5.c
    ad2antrr
    wph
    @52
    @58
    @63
    opphllem5.r
    ad2antrr
    wph
    cS
    cD
    wcel
    #
    @58
    @63
    opphllem5.s
    ad2antrr
    wph
    @12
    @58
    @63
    opphllem5.m
    ad2antrr
    wph
    @57
    @58
    @63
    opphllem5.o
    ad2antrr
    wph
    cD
    @17
    @50
    wbr
    #
    @58
    @63
    opphllem5.p
    ad2antrr
    wph
    cD
    @26
    @50
    wbr
    #
    @58
    @63
    opphllem5.q
    ad2antrr
    @59
    @58
    @63
    wph
    @58
    simpr
    #
    adantr
    @59
    @63
    simpr
    wph
    @15
    @58
    @63
    opphllem5.u
    ad2antrr
    wph
    @22
    @58
    @63
    opphllem6.v
    ad2antrr
    opphllem3
    @59
    @64
    wa
    #
    @4
    @2
    cN
    cfv
    #
    cA
    @0
    wbr
    @1
    @69
    vt
    cC
    cA
    cD
    cP
    cS
    cR
    @2
    cG
    cI
    cK
    cL
    cM
    c.mi
    cN
    cO
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    wph
    @43
    @58
    @64
    opphl.d
    ad2antrr
    #
    @59
    @11
    @64
    wph
    @11
    @58
    opphl.g
    adantr
    adantr
    #
    opphl.k
    opphllem5.n
    wph
    @14
    @58
    @64
    opphllem5.c
    ad2antrr
    #
    @59
    @13
    @64
    wph
    @13
    @58
    opphllem5.a
    adantr
    adantr
    #
    @59
    @65
    @64
    wph
    @65
    @58
    opphllem5.s
    adantr
    adantr
    @59
    @52
    @64
    wph
    @52
    @58
    opphllem5.r
    adantr
    adantr
    wph
    @12
    @58
    @64
    opphllem5.m
    ad2antrr
    #
    @69
    vt
    cA
    cC
    cD
    cP
    cG
    cI
    cL
    c.mi
    cO
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    @71
    @72
    @74
    @73
    wph
    @57
    @58
    @64
    opphllem5.o
    ad2antrr
    oppcom
    wph
    @67
    @58
    @64
    opphllem5.q
    ad2antrr
    @59
    @66
    @64
    wph
    @66
    @58
    opphllem5.p
    adantr
    adantr
    @59
    cS
    cR
    wne
    @64
    @59
    cR
    cS
    @68
    necomd
    adantr
    @59
    @64
    simpr
    @69
    cM
    cP
    @9
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
    @10
    @72
    @75
    opphllem5.n
    wph
    @15
    @58
    @64
    opphllem5.u
    ad2antrr
    #
    mircl
    @69
    cM
    cR
    cS
    cP
    @9
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @10
    @72
    @75
    opphllem5.n
    @59
    @41
    @64
    wph
    @41
    @58
    @16
    adantr
    adantr
    wph
    @22
    @58
    @64
    opphllem6.v
    ad2antrr
    mircom
    opphllem3
    @69
    @70
    cU
    cA
    @0
    @69
    cM
    cU
    cP
    @9
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @10
    @72
    @75
    opphllem5.n
    @76
    mirmir
    breq1d
    bitr2d
    wph
    @63
    @64
    wo
    @58
    wph
    cS
    cC
    cR
    cA
    cP
    cG
    cI
    @62
    c.mi
    hpg.p
    hpg.d
    hpg.i
    @62
    eqid
    opphl.g
    @25
    opphllem5.c
    @16
    opphllem5.a
    legtrid
    adantr
    mpjaodan
    pm2.61dane
end
