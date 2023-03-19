include "cv.mm"
include "wne.mm"
include "co.mm"
include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "simprrl.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "crn.mm"
include "tglnpt.mm"
include "simplr.mm"
include "simpr.mm"
include "tglinethru.mm"
include "adantr.mm"
include "breqtrrd.mm"
include "wn.mm"
include "ad3antrrr.mm"
include "simprl.mm"
include "footne.mm"
include "neneqd.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"
include "eleqtrrd.mm"
include "simprrr.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "imp.mm"
include "anasss.mm"
include "jca31.mm"
include "wb.mm"
include "islnopp.mm"
include "mpbird.mm"
include "c2.mm"
include "cstrkgld.mm"
include "colperpex.mm"
include "reximddv.mm"
include "tglnpt2.mm"
include "r19.29a.mm"

theorem oppperpex
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cR: class R
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
  assume oppperpex.1: |- ( ph -> A e. D )
  assume oppperpex.2: |- ( ph -> C e. P )
  assume oppperpex.3: |- ( ph -> -. C e. D )
  assume oppperpex.4: |- ( ph -> G TarskiGDim>= 2 )

  disjoint L p
  disjoint D a
  disjoint D b
  disjoint a b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint P b
  disjoint A p
  disjoint A t
  disjoint p t
  disjoint D p
  disjoint D t
  disjoint C p
  disjoint C t
  disjoint G p
  disjoint G t
  disjoint L t
  disjoint I p
  disjoint I t
  disjoint K p
  disjoint K t
  disjoint O t
  disjoint P p
  disjoint P t
  disjoint p ph
  disjoint ph t
  disjoint .- p
  disjoint .- t
  disjoint a t
  disjoint b t
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint m p
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint m z
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
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R m
  disjoint R p
  disjoint R t
  disjoint C m
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint G m
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
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint M t
  disjoint O m
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint N m
  disjoint N p
  disjoint N t
  disjoint P m
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S m
  disjoint S p
  disjoint S t
  disjoint V m
  disjoint V t
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .- m
  disjoint .- x
  disjoint .- y
  disjoint .- z
  assert |- ( ph -> E. p e. P ( ( A L p ) ( perpG ` G ) D /\ C O p ) )

  proof
    wph
    cA
    vx
    cv
    #
    wne
    #
    cA
    vp
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
    cC
    @2
    cO
    wbr
    #
    wa
    #
    vp
    cP
    wrex
    vx
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
    @3
    cA
    @0
    cL
    co
    #
    @4
    wbr
    #
    vt
    cv
    #
    @11
    wcel
    #
    cA
    @0
    wceq
    #
    wo
    #
    @13
    cC
    @2
    cI
    co
    wcel
    #
    wa
    #
    vt
    cP
    wrex
    #
    wa
    #
    @7
    vp
    cP
    @10
    @2
    cP
    wcel
    #
    @20
    wa
    #
    wa
    #
    @5
    @6
    @23
    @3
    @11
    cD
    @4
    @10
    @21
    @12
    @19
    simprrl
    @10
    cD
    @11
    wceq
    #
    @22
    @10
    cD
    cP
    cA
    @0
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    wph
    cG
    cstrkg
    wcel
    #
    @8
    @1
    opphl.g
    ad2antrr
    #
    @10
    cD
    cP
    cG
    cI
    cL
    cA
    hpg.p
    opphl.l
    hpg.i
    @26
    wph
    cD
    cL
    crn
    wcel
    #
    @8
    @1
    opphl.d
    ad2antrr
    #
    wph
    cA
    cD
    wcel
    #
    @8
    @1
    oppperpex.1
    ad2antrr
    #
    tglnpt
    #
    @10
    cD
    cP
    cG
    cI
    cL
    @0
    hpg.p
    opphl.l
    hpg.i
    @26
    @28
    wph
    @8
    @1
    simplr
    #
    tglnpt
    #
    @9
    @1
    simpr
    #
    @34
    @28
    @30
    @32
    tglinethru
    #
    adantr
    breqtrrd
    #
    @23
    @6
    cC
    cD
    wcel
    wn
    #
    @2
    cD
    wcel
    wn
    #
    wa
    @17
    vt
    cD
    wrex
    #
    wa
    #
    @23
    @37
    @38
    @39
    wph
    @37
    @8
    @1
    @22
    oppperpex.3
    ad3antrrr
    @23
    cD
    cP
    cG
    cI
    cL
    c.mi
    cA
    @2
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @10
    @25
    @22
    @26
    adantr
    @10
    @27
    @22
    @28
    adantr
    @10
    @29
    @22
    @30
    adantr
    @10
    @21
    @20
    simprl
    @36
    footne
    @10
    @21
    @20
    @39
    @10
    @21
    wa
    #
    @12
    @19
    @39
    @41
    @12
    wa
    #
    @19
    @39
    @42
    @18
    @17
    vt
    cP
    cD
    @42
    @13
    cP
    wcel
    #
    @18
    wa
    #
    @13
    cD
    wcel
    #
    @17
    wa
    @42
    @44
    wa
    #
    @45
    @17
    @46
    @13
    @11
    cD
    @46
    @15
    wn
    @14
    @46
    cA
    @0
    @10
    @1
    @21
    @12
    @44
    @34
    ad3antrrr
    neneqd
    @46
    @15
    @14
    @46
    @14
    @15
    @42
    @43
    @16
    @17
    simprrl
    orcomd
    ord
    mpd
    @10
    @24
    @21
    @12
    @44
    @35
    ad3antrrr
    eleqtrrd
    @42
    @43
    @16
    @17
    simprrr
    jca
    ex
    reximdv2
    imp
    anasss
    anasss
    jca31
    @10
    @21
    @20
    @6
    @40
    wb
    #
    @41
    @12
    @19
    @47
    @42
    @47
    @19
    @42
    vt
    cC
    @2
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
    @10
    cC
    cP
    wcel
    #
    @21
    @12
    wph
    @48
    @8
    @1
    oppperpex.2
    ad2antrr
    #
    ad2antrr
    @10
    @21
    @12
    simplr
    islnopp
    adantr
    anasss
    anasss
    mpbird
    jca
    @10
    vt
    cA
    @0
    cC
    cP
    cG
    cI
    cL
    c.mi
    vp
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @26
    @31
    @33
    @49
    @34
    wph
    cG
    c2
    cstrkgld
    wbr
    @8
    @1
    oppperpex.4
    ad2antrr
    colperpex
    reximddv
    wph
    vx
    cD
    cP
    cG
    cI
    cL
    cA
    hpg.p
    hpg.i
    opphl.l
    opphl.g
    opphl.d
    oppperpex.1
    tglnpt2
    r19.29a
end
