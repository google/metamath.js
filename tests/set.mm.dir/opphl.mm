include "cv.mm"
include "co.mm"
include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cmir.mm"
include "wceq.mm"
include "crn.mm"
include "ad8antr.mm"
include "cstrkg.mm"
include "eqid.mm"
include "simp-4r.mm"
include "mircl.mm"
include "simplr.mm"
include "simp-6r.mm"
include "simp-8r.mm"
include "simp-7r.mm"
include "perpln1.mm"
include "perpcom.mm"
include "simp-5r.mm"
include "tglnpt.mm"
include "tglnne.mm"
include "hlid.mm"
include "simpllr.mm"
include "eqcomd.mm"
include "opphllem6.mm"
include "mpbid.mm"
include "opphllem5.mm"
include "eqeltrd.mm"
include "mirln2.mm"
include "mirmir.mm"
include "wne.mm"
include "hlne1.mm"
include "hlln.mm"
include "tglngne.mm"
include "wo.mm"
include "w3a.mm"
include "ishlg.mm"
include "simp3d.mm"
include "opphllem2.mm"
include "simpr.mm"
include "tglinerflx2.mm"
include "tglinethru.mm"
include "breqtrd.mm"
include "hlcomd.mm"
include "wrex.mm"
include "oppne1.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "mtand.mm"
include "footex.mm"
include "ad6antr.mm"
include "r19.29a.mm"
include "ad4antr.mm"
include "c2.mm"
include "cstrkgld.mm"
include "opptgdim2.mm"
include "midex.mm"
include "oppne2.mm"
include "ad2antrr.mm"

theorem opphl
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vp: setvar p
  let cU: class U
  let cM: class M
  let cN: class N
  let cS: class S
  let cV: class V
  assume hpg.p: |- P = ( Base ` G )
  assume hpg.d: |- .- = ( dist ` G )
  assume hpg.i: |- I = ( Itv ` G )
  assume hpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume opphl.l: |- L = ( LineG ` G )
  assume opphl.d: |- ( ph -> D e. ran L )
  assume opphl.g: |- ( ph -> G e. TarskiG )
  assume opphl.k: |- K = ( hlG ` G )
  assume opphl.a: |- ( ph -> A e. P )
  assume opphl.b: |- ( ph -> B e. P )
  assume opphl.c: |- ( ph -> C e. P )
  assume opphl.1: |- ( ph -> A O C )
  assume opphl.2: |- ( ph -> R e. D )
  assume opphl.3: |- ( ph -> A ( K ` R ) B )

  disjoint D a
  disjoint D b
  disjoint a b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint P b
  disjoint A t
  disjoint B t
  disjoint D t
  disjoint R t
  disjoint C t
  disjoint G t
  disjoint L t
  disjoint I t
  disjoint K t
  disjoint O t
  disjoint P t
  disjoint ph t
  disjoint .- t
  disjoint a t
  disjoint b t
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint x y
  disjoint x z
  disjoint y z
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
  disjoint U t
  disjoint I m
  disjoint I p
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint K p
  disjoint M t
  disjoint O m
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint N m
  disjoint N p
  disjoint N t
  disjoint P m
  disjoint P p
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S m
  disjoint S p
  disjoint S t
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
  assert |- ( ph -> B O C )

  proof
    wph
    cA
    vx
    cv
    #
    cL
    co
    #
    cD
    cG
    cperpg
    cfv
    #
    wbr
    #
    cB
    cC
    cO
    wbr
    #
    vx
    cD
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @3
    wa
    #
    cC
    vz
    cv
    #
    cL
    co
    #
    cD
    @2
    wbr
    #
    @4
    vz
    cD
    @7
    @8
    cD
    wcel
    #
    wa
    #
    @10
    wa
    #
    @8
    @0
    vm
    cv
    #
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    wceq
    #
    @4
    vm
    cP
    @13
    @14
    cP
    wcel
    #
    wa
    #
    @18
    wa
    #
    cB
    vy
    cv
    #
    cL
    co
    #
    cD
    @2
    wbr
    #
    @4
    vy
    cD
    @21
    @22
    cD
    wcel
    #
    wa
    #
    @24
    wa
    #
    vt
    cB
    cA
    @16
    cfv
    #
    cD
    cP
    @22
    @8
    cB
    cG
    cI
    cK
    cL
    @14
    c.mi
    @16
    cO
    cC
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    wph
    cD
    cL
    crn
    wcel
    #
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    opphl.d
    ad8antr
    #
    wph
    cG
    cstrkg
    wcel
    #
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    opphl.g
    ad8antr
    #
    opphl.k
    @16
    eqid
    #
    wph
    cB
    cP
    wcel
    #
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    opphl.b
    ad8antr
    #
    @27
    @14
    cP
    @15
    cG
    cI
    cL
    @16
    c.mi
    cA
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @15
    eqid
    #
    @32
    @13
    @19
    @18
    @25
    @24
    simp-4r
    #
    @33
    wph
    cA
    cP
    wcel
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    opphl.a
    ad8antr
    #
    mircl
    #
    @21
    @25
    @24
    simplr
    #
    @7
    @11
    @10
    @19
    @18
    @25
    @24
    simp-6r
    #
    @37
    @27
    vt
    cA
    cB
    @28
    cD
    cP
    cR
    @16
    cG
    cI
    cL
    @14
    c.mi
    cO
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    @30
    @32
    @33
    @38
    @35
    @39
    wph
    cR
    cD
    wcel
    #
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    opphl.2
    ad8antr
    @27
    vt
    cA
    cC
    cD
    cP
    @0
    @8
    cA
    cG
    cI
    cK
    cL
    @14
    c.mi
    @16
    cO
    @28
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    @30
    @32
    opphl.k
    @33
    @38
    wph
    cC
    cP
    wcel
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    opphl.c
    ad8antr
    #
    wph
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    simp-8r
    #
    @41
    @37
    wph
    cA
    cC
    cO
    wbr
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    opphl.1
    ad8antr
    #
    @27
    @1
    cD
    cP
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @32
    @27
    @1
    cD
    cG
    cL
    opphl.l
    @32
    @6
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    simp-7r
    #
    perpln1
    #
    @30
    @46
    perpcom
    #
    @27
    @9
    cD
    cP
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @32
    @27
    @9
    cD
    cG
    cL
    opphl.l
    @32
    @12
    @10
    @19
    @18
    @25
    @24
    simp-5r
    #
    perpln1
    #
    @30
    @49
    perpcom
    #
    @38
    @39
    @27
    cA
    cA
    @0
    cP
    cG
    cI
    cK
    hpg.p
    hpg.i
    opphl.k
    @38
    @38
    @27
    cD
    cP
    cG
    cI
    cL
    @0
    hpg.p
    opphl.l
    hpg.i
    @32
    @30
    @44
    tglnpt
    #
    @32
    @27
    cP
    cG
    cI
    cL
    cA
    @0
    hpg.p
    hpg.i
    opphl.l
    @32
    @38
    @52
    @47
    tglnne
    hlid
    #
    @27
    cA
    cA
    @0
    cK
    cfv
    wbr
    @28
    cC
    @8
    cK
    cfv
    wbr
    @53
    @27
    vt
    cA
    cC
    cD
    cP
    @0
    @8
    cA
    cG
    cI
    cK
    cL
    @14
    c.mi
    @16
    cO
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    @30
    @32
    opphl.k
    @33
    @38
    @43
    @44
    @41
    @37
    @45
    @48
    @51
    @38
    @27
    @8
    @17
    @20
    @18
    @25
    @24
    simpllr
    eqcomd
    #
    opphllem6
    mpbid
    #
    opphllem5
    @27
    @14
    @0
    cD
    cP
    @15
    cG
    cI
    cL
    @16
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @36
    @32
    @33
    @30
    @37
    @44
    @27
    @17
    @8
    cD
    @54
    @41
    eqeltrd
    mirln2
    @27
    @28
    @16
    cfv
    cA
    @27
    @14
    cA
    cP
    @15
    cG
    cI
    cL
    @16
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @36
    @32
    @37
    @33
    @38
    mirmir
    eqcomd
    wph
    cA
    cR
    wne
    #
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    wph
    cA
    cB
    cR
    cP
    cG
    cI
    cK
    cstrkg
    hpg.p
    hpg.i
    opphl.k
    opphl.a
    opphl.b
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
    opphl.2
    tglnpt
    #
    opphl.g
    opphl.3
    hlne1
    ad8antr
    wph
    cB
    cR
    wne
    #
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    wph
    cP
    cG
    cI
    cL
    cB
    cR
    cA
    hpg.p
    opphl.l
    hpg.i
    opphl.g
    opphl.b
    @57
    wph
    cA
    cB
    cR
    cP
    cG
    cI
    cK
    cL
    hpg.p
    hpg.i
    opphl.k
    opphl.a
    opphl.b
    @57
    opphl.g
    opphl.l
    opphl.3
    hlln
    #
    tglngne
    #
    ad8antr
    wph
    cA
    cR
    cB
    cI
    co
    wcel
    cB
    cR
    cA
    cI
    co
    wcel
    wo
    #
    @5
    @3
    @11
    @10
    @19
    @18
    @25
    @24
    wph
    @56
    @58
    @61
    wph
    cA
    cB
    cR
    cK
    cfv
    wbr
    @56
    @58
    @61
    w3a
    opphl.3
    wph
    cA
    cB
    cR
    cP
    cG
    cI
    cK
    cstrkg
    hpg.p
    hpg.i
    opphl.k
    opphl.a
    opphl.b
    @57
    opphl.g
    ishlg
    mpbid
    simp3d
    ad8antr
    opphllem2
    @27
    @23
    cD
    cP
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @32
    @27
    @23
    cD
    cG
    cL
    opphl.l
    @32
    @26
    @24
    simpr
    #
    perpln1
    #
    @30
    @62
    perpcom
    @27
    cD
    @9
    @28
    @8
    cL
    co
    @2
    @51
    @27
    @9
    cP
    @28
    @8
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    @32
    @39
    @27
    cD
    cP
    cG
    cI
    cL
    @8
    hpg.p
    opphl.l
    hpg.i
    @32
    @30
    @41
    tglnpt
    #
    @27
    @28
    cC
    @8
    cP
    cG
    cI
    cK
    cstrkg
    hpg.p
    hpg.i
    opphl.k
    @39
    @43
    @64
    @32
    @55
    hlne1
    #
    @65
    @50
    @27
    @28
    cC
    @8
    cP
    cG
    cI
    cK
    cL
    hpg.p
    hpg.i
    opphl.k
    @39
    @43
    @64
    @32
    opphl.l
    @55
    hlln
    #
    @27
    cP
    cC
    @8
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    @32
    @43
    @64
    @27
    cP
    cG
    cI
    cL
    cC
    @8
    @28
    hpg.p
    opphl.l
    hpg.i
    @32
    @43
    @64
    @66
    tglngne
    tglinerflx2
    tglinethru
    breqtrd
    @35
    @43
    @27
    cB
    cA
    @22
    cP
    cG
    cI
    cK
    hpg.p
    hpg.i
    opphl.k
    @35
    @38
    @27
    cD
    cP
    cG
    cI
    cL
    @22
    hpg.p
    opphl.l
    hpg.i
    @32
    @30
    @40
    tglnpt
    #
    @32
    @27
    cP
    cG
    cI
    cL
    cB
    @22
    hpg.p
    hpg.i
    opphl.l
    @32
    @35
    @67
    @63
    tglnne
    hlid
    @27
    @28
    cC
    @8
    cP
    cG
    cI
    cK
    cstrkg
    hpg.p
    hpg.i
    opphl.k
    @39
    @43
    @64
    @32
    @55
    hlcomd
    opphllem5
    wph
    @24
    vy
    cD
    wrex
    @5
    @3
    @11
    @10
    @19
    @18
    wph
    vy
    cD
    cB
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
    opphl.b
    wph
    cB
    cD
    wcel
    #
    cA
    cD
    wcel
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
    opphl.a
    opphl.c
    opphl.1
    oppne1
    #
    wph
    @68
    wa
    #
    cA
    cB
    cR
    cL
    co
    #
    cD
    wph
    cA
    @71
    wcel
    @68
    @59
    adantr
    @70
    cD
    cP
    cB
    cR
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    wph
    @31
    @68
    opphl.g
    adantr
    wph
    @34
    @68
    opphl.b
    adantr
    wph
    cR
    cP
    wcel
    @68
    @57
    adantr
    wph
    @58
    @68
    @60
    adantr
    #
    @72
    wph
    @29
    @68
    opphl.d
    adantr
    wph
    @68
    simpr
    wph
    @42
    @68
    opphl.2
    adantr
    tglinethru
    eleqtrrd
    mtand
    footex
    ad6antr
    r19.29a
    @13
    vm
    @0
    @8
    cP
    @15
    cG
    cI
    cL
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    wph
    @31
    @5
    @3
    @11
    @10
    opphl.g
    ad4antr
    #
    @36
    @13
    cD
    cP
    cG
    cI
    cL
    @0
    hpg.p
    opphl.l
    hpg.i
    @73
    wph
    @29
    @5
    @3
    @11
    @10
    opphl.d
    ad4antr
    #
    wph
    @5
    @3
    @11
    @10
    simp-4r
    tglnpt
    @13
    cD
    cP
    cG
    cI
    cL
    @8
    hpg.p
    opphl.l
    hpg.i
    @73
    @74
    @7
    @11
    @10
    simplr
    tglnpt
    wph
    cG
    c2
    cstrkgld
    wbr
    @5
    @3
    @11
    @10
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
    opphl.a
    opphl.c
    opphl.1
    opptgdim2
    ad4antr
    midex
    r19.29a
    wph
    @10
    vz
    cD
    wrex
    @5
    @3
    wph
    vz
    cD
    cC
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
    opphl.c
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
    opphl.a
    opphl.c
    opphl.1
    oppne2
    footex
    ad2antrr
    r19.29a
    wph
    vx
    cD
    cA
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
    opphl.a
    @69
    footex
    r19.29a
end
