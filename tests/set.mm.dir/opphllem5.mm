include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "cperpg.mm"
include "cfv.mm"
include "tglnpt.mm"
include "cstrkg.mm"
include "hlne2.mm"
include "tglinecom.mm"
include "breqtrd.mm"
include "hlcomd.mm"
include "hlperpnel.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "simpr.mm"
include "wne.mm"
include "cmir.mm"
include "eqid.mm"
include "adantr.mm"
include "crn.mm"
include "simpllr.mm"
include "tglinerflx2.mm"
include "eqeltrd.mm"
include "tgelrnln.mm"
include "perpcom.mm"
include "ad4antr.mm"
include "tglinethru.mm"
include "perprag.mm"
include "tgbtwncom.mm"
include "ragflat2.mm"
include "pm2.61dane.mm"
include "fveq2d.mm"
include "breqd.mm"
include "mpbird.mm"
include "btwnhl.mm"
include "eqeltrrd.mm"
include "rspe.mm"
include "syl2anc.mm"
include "jca31.mm"
include "wb.mm"
include "islnopp.mm"
include "mpbid.mm"
include "simprd.mm"
include "r19.29a.mm"
include "cleg.mm"
include "eqcomd.mm"
include "opphllem4.mm"
include "oppcom.mm"
include "necomd.mm"
include "mircom.mm"
include "wo.mm"
include "legtrid.mm"
include "mpjaodan.mm"
include "c2.mm"
include "cstrkgld.mm"
include "opptgdim2.mm"
include "midex.mm"

theorem opphllem5
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
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
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
  assume opphllem5.v: |- ( ph -> V e. P )
  assume opphllem5.1: |- ( ph -> U ( K ` R ) A )
  assume opphllem5.2: |- ( ph -> V ( K ` S ) C )

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
  disjoint V t
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
  assert |- ( ph -> U O V )

  proof
    wph
    cU
    cV
    cO
    wbr
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
    vt
    cv
    #
    cA
    cC
    cI
    co
    #
    wcel
    #
    @0
    vt
    cD
    @2
    @3
    cD
    wcel
    #
    wa
    #
    @5
    wa
    #
    @0
    cU
    cD
    wcel
    wn
    #
    cV
    cD
    wcel
    wn
    #
    wa
    @3
    cU
    cV
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    #
    @8
    @9
    @10
    @13
    wph
    @9
    @1
    @6
    @5
    wph
    cD
    cP
    cR
    cG
    cI
    cK
    cL
    c.mi
    cA
    cU
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    opphl.g
    opphl.d
    opphl.k
    opphllem5.r
    opphllem5.a
    opphllem5.u
    wph
    cD
    cA
    cR
    cL
    co
    #
    cR
    cA
    cL
    co
    cG
    cperpg
    cfv
    #
    opphllem5.p
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
    cU
    cA
    cR
    cP
    cG
    cI
    cK
    cstrkg
    hpg.p
    hpg.i
    opphl.k
    opphllem5.u
    opphllem5.a
    @17
    opphl.g
    opphllem5.1
    hlne2
    #
    tglinecom
    breqtrd
    wph
    cU
    cA
    cR
    cP
    cG
    cI
    cK
    cstrkg
    hpg.p
    hpg.i
    opphl.k
    opphllem5.u
    opphllem5.a
    @17
    opphl.g
    opphllem5.1
    hlcomd
    #
    hlperpnel
    ad3antrrr
    wph
    @10
    @1
    @6
    @5
    wph
    cD
    cP
    cS
    cG
    cI
    cK
    cL
    c.mi
    cC
    cV
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    opphl.g
    opphl.d
    opphl.k
    opphllem5.s
    opphllem5.c
    opphllem5.v
    wph
    cD
    cC
    cS
    cL
    co
    #
    cS
    cC
    cL
    co
    @16
    opphllem5.q
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
    cV
    cC
    cS
    cP
    cG
    cI
    cK
    cstrkg
    hpg.p
    hpg.i
    opphl.k
    opphllem5.v
    opphllem5.c
    @21
    opphl.g
    opphllem5.2
    hlne2
    #
    tglinecom
    breqtrd
    wph
    cV
    cC
    cS
    cP
    cG
    cI
    cK
    cstrkg
    hpg.p
    hpg.i
    opphl.k
    opphllem5.v
    opphllem5.c
    @21
    opphl.g
    opphllem5.2
    hlcomd
    hlperpnel
    ad3antrrr
    @8
    @6
    @12
    @13
    @2
    @6
    @5
    simplr
    #
    @8
    cR
    @3
    @11
    @8
    cR
    @3
    wceq
    #
    cR
    @3
    @8
    @24
    simpr
    @8
    cR
    @3
    wne
    #
    wa
    #
    cC
    cR
    @3
    cA
    cP
    cG
    cmir
    cfv
    #
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @27
    eqid
    #
    @8
    cG
    cstrkg
    wcel
    #
    @25
    wph
    @29
    @1
    @6
    @5
    opphl.g
    ad3antrrr
    #
    adantr
    #
    @8
    cC
    cP
    wcel
    #
    @25
    wph
    @32
    @1
    @6
    @5
    opphllem5.c
    ad3antrrr
    #
    adantr
    #
    @8
    cR
    cP
    wcel
    #
    @25
    wph
    @35
    @1
    @6
    @5
    @17
    ad3antrrr
    #
    adantr
    #
    @8
    @3
    cP
    wcel
    @25
    @8
    cD
    cP
    cG
    cI
    cL
    @3
    hpg.p
    opphl.l
    hpg.i
    @30
    wph
    cD
    cL
    crn
    wcel
    #
    @1
    @6
    @5
    opphl.d
    ad3antrrr
    #
    @23
    tglnpt
    adantr
    #
    @8
    cA
    cP
    wcel
    #
    @25
    wph
    @41
    @1
    @6
    @5
    opphllem5.a
    ad3antrrr
    #
    adantr
    #
    @26
    cC
    cS
    cR
    @3
    cP
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @31
    @34
    @8
    cS
    cP
    wcel
    #
    @25
    wph
    @44
    @1
    @6
    @5
    @21
    ad3antrrr
    adantr
    @8
    cR
    @20
    wcel
    @25
    @8
    cR
    cS
    @20
    wph
    @1
    @6
    @5
    simpllr
    #
    wph
    cS
    @20
    wcel
    @1
    @6
    @5
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
    @21
    @22
    tglinerflx2
    ad3antrrr
    eqeltrd
    adantr
    @40
    @26
    @20
    cD
    cR
    @3
    cL
    co
    #
    @16
    wph
    @20
    cD
    @16
    wbr
    @1
    @6
    @5
    @25
    wph
    cD
    @20
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
    @21
    @22
    tgelrnln
    opphllem5.q
    perpcom
    ad4antr
    @26
    cD
    cP
    cR
    @3
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    @31
    @37
    @40
    @8
    @25
    simpr
    #
    @47
    @8
    @38
    @25
    @39
    adantr
    @8
    cR
    cD
    wcel
    #
    @25
    wph
    @48
    @1
    @6
    @5
    opphllem5.r
    ad3antrrr
    adantr
    @8
    @6
    @25
    @23
    adantr
    tglinethru
    #
    breqtrd
    perprag
    @26
    cA
    cR
    cR
    @3
    cP
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @31
    @43
    @37
    @8
    cR
    @15
    wcel
    #
    @25
    wph
    @50
    @1
    @6
    @5
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
    @17
    @18
    tglinerflx2
    ad3antrrr
    adantr
    @40
    @26
    @15
    cD
    @46
    @16
    wph
    @15
    cD
    @16
    wbr
    @1
    @6
    @5
    @25
    wph
    cD
    @15
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
    @17
    @18
    tgelrnln
    opphllem5.p
    perpcom
    ad4antr
    @49
    breqtrd
    perprag
    @26
    cA
    @3
    cC
    cP
    cG
    cI
    c.mi
    hpg.p
    hpg.d
    hpg.i
    @31
    @43
    @40
    @34
    @7
    @5
    @25
    simplr
    tgbtwncom
    ragflat2
    pm2.61dane
    #
    @8
    cA
    cU
    cV
    cR
    cP
    cG
    cI
    cK
    hpg.p
    hpg.i
    opphl.k
    @42
    wph
    cU
    cP
    wcel
    #
    @1
    @6
    @5
    opphllem5.u
    ad3antrrr
    wph
    cV
    cP
    wcel
    #
    @1
    @6
    @5
    opphllem5.v
    ad3antrrr
    #
    @30
    @36
    wph
    cA
    cU
    cR
    cK
    cfv
    #
    wbr
    @1
    @6
    @5
    @19
    ad3antrrr
    @8
    cV
    cR
    cA
    cP
    cG
    cI
    c.mi
    hpg.p
    hpg.d
    hpg.i
    @30
    @54
    @36
    @42
    @8
    cC
    cV
    cA
    cR
    cP
    cG
    cI
    cK
    hpg.p
    hpg.i
    opphl.k
    @33
    @54
    @42
    @30
    @36
    @8
    cV
    cC
    cR
    cP
    cG
    cI
    cK
    cstrkg
    hpg.p
    hpg.i
    opphl.k
    @54
    @33
    @36
    @30
    @8
    cV
    cC
    @55
    wbr
    cV
    cC
    cS
    cK
    cfv
    #
    wbr
    #
    wph
    @57
    @1
    @6
    @5
    opphllem5.2
    ad3antrrr
    @8
    @55
    @56
    cV
    cC
    @8
    cR
    cS
    cK
    @45
    fveq2d
    breqd
    mpbird
    hlcomd
    @8
    cA
    cR
    cC
    cP
    cG
    cI
    c.mi
    hpg.p
    hpg.d
    hpg.i
    @30
    @42
    @36
    @33
    @8
    cR
    @3
    @4
    @51
    @7
    @5
    simpr
    eqeltrd
    tgbtwncom
    btwnhl
    tgbtwncom
    btwnhl
    eqeltrrd
    @12
    vt
    cD
    rspe
    syl2anc
    jca31
    wph
    @0
    @14
    wb
    @1
    @6
    @5
    wph
    vt
    cU
    cV
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
    opphllem5.u
    opphllem5.v
    islnopp
    ad3antrrr
    mpbird
    wph
    @5
    vt
    cD
    wrex
    #
    @1
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
    @58
    wph
    cA
    cC
    cO
    wbr
    #
    @59
    @58
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
    wph
    cR
    cS
    wne
    #
    wa
    #
    cS
    cR
    vm
    cv
    #
    @27
    cfv
    #
    cfv
    #
    wceq
    #
    @0
    vm
    cP
    @62
    @63
    cP
    wcel
    #
    wa
    #
    @66
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
    @0
    @71
    @70
    @72
    wbr
    #
    @69
    @73
    wa
    #
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
    @63
    c.mi
    @64
    cO
    cV
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    wph
    @38
    @61
    @67
    @66
    @73
    opphl.d
    ad4antr
    wph
    @29
    @61
    @67
    @66
    @73
    opphl.g
    ad4antr
    opphl.k
    @64
    eqid
    #
    wph
    @41
    @61
    @67
    @66
    @73
    opphllem5.a
    ad4antr
    wph
    @32
    @61
    @67
    @66
    @73
    opphllem5.c
    ad4antr
    wph
    @48
    @61
    @67
    @66
    @73
    opphllem5.r
    ad4antr
    wph
    cS
    cD
    wcel
    #
    @61
    @67
    @66
    @73
    opphllem5.s
    ad4antr
    @62
    @67
    @66
    @73
    simpllr
    wph
    @60
    @61
    @67
    @66
    @73
    opphllem5.o
    ad4antr
    wph
    cD
    @15
    @16
    wbr
    #
    @61
    @67
    @66
    @73
    opphllem5.p
    ad4antr
    wph
    cD
    @20
    @16
    wbr
    #
    @61
    @67
    @66
    @73
    opphllem5.q
    ad4antr
    @62
    @61
    @67
    @66
    @73
    wph
    @61
    simpr
    #
    ad3antrrr
    @69
    @73
    simpr
    wph
    @52
    @61
    @67
    @66
    @73
    opphllem5.u
    ad4antr
    @75
    cS
    @65
    @68
    @66
    @73
    simplr
    eqcomd
    wph
    @53
    @61
    @67
    @66
    @73
    opphllem5.v
    ad4antr
    wph
    cU
    cA
    @55
    wbr
    #
    @61
    @67
    @66
    @73
    opphllem5.1
    ad4antr
    wph
    @57
    @61
    @67
    @66
    @73
    opphllem5.2
    ad4antr
    opphllem4
    @69
    @74
    wa
    #
    vt
    cV
    cU
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
    wph
    @38
    @61
    @67
    @66
    @74
    opphl.d
    ad4antr
    #
    @62
    @29
    @67
    @66
    @74
    wph
    @29
    @61
    opphl.g
    adantr
    #
    ad3antrrr
    #
    wph
    @53
    @61
    @67
    @66
    @74
    opphllem5.v
    ad4antr
    #
    wph
    @52
    @61
    @67
    @66
    @74
    opphllem5.u
    ad4antr
    #
    @82
    vt
    cC
    cA
    cD
    cP
    cS
    cR
    cV
    cG
    cI
    cK
    cL
    @63
    c.mi
    @64
    cO
    cU
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    @83
    @85
    opphl.k
    @76
    wph
    @32
    @61
    @67
    @66
    @74
    opphllem5.c
    ad4antr
    #
    @62
    @41
    @67
    @66
    @74
    wph
    @41
    @61
    opphllem5.a
    adantr
    ad3antrrr
    #
    @62
    @77
    @67
    @66
    @74
    wph
    @77
    @61
    opphllem5.s
    adantr
    ad3antrrr
    @62
    @48
    @67
    @66
    @74
    wph
    @48
    @61
    opphllem5.r
    adantr
    ad3antrrr
    @62
    @67
    @66
    @74
    simpllr
    #
    @82
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
    @83
    @85
    @89
    @88
    wph
    @60
    @61
    @67
    @66
    @74
    opphllem5.o
    ad4antr
    oppcom
    wph
    @79
    @61
    @67
    @66
    @74
    opphllem5.q
    ad4antr
    @62
    @78
    @67
    @66
    @74
    wph
    @78
    @61
    opphllem5.p
    adantr
    ad3antrrr
    @62
    cS
    cR
    wne
    @67
    @66
    @74
    @62
    cR
    cS
    @80
    necomd
    ad3antrrr
    @69
    @74
    simpr
    @86
    @82
    @63
    cR
    cS
    cP
    @27
    cG
    cI
    cL
    @64
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @28
    @85
    @90
    @76
    @62
    @35
    @67
    @66
    @74
    wph
    @35
    @61
    @17
    adantr
    #
    ad3antrrr
    @82
    cS
    @65
    @68
    @66
    @74
    simplr
    eqcomd
    mircom
    @87
    wph
    @57
    @61
    @67
    @66
    @74
    opphllem5.2
    ad4antr
    wph
    @81
    @61
    @67
    @66
    @74
    opphllem5.1
    ad4antr
    opphllem4
    oppcom
    wph
    @73
    @74
    wo
    @61
    @67
    @66
    wph
    cS
    cC
    cR
    cA
    cP
    cG
    cI
    @72
    c.mi
    hpg.p
    hpg.d
    hpg.i
    @72
    eqid
    opphl.g
    @21
    opphllem5.c
    @17
    opphllem5.a
    legtrid
    ad3antrrr
    mpjaodan
    @62
    vm
    cR
    cS
    cP
    @27
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @84
    @28
    @91
    wph
    @44
    @61
    @21
    adantr
    wph
    cG
    c2
    cstrkgld
    wbr
    @61
    wph
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
    opphl.d
    opphl.g
    opphllem5.a
    opphllem5.c
    opphllem5.o
    opptgdim2
    adantr
    midex
    r19.29a
    pm2.61dane
end
