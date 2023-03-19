include "co.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "crn.mm"
include "adantr.mm"
include "cstrkg.mm"
include "cfv.mm"
include "cmir.mm"
include "eqid.mm"
include "tglnpt.mm"
include "mircl.mm"
include "mirln.mm"
include "wceq.mm"
include "simpr.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "ad3antrrr.mm"
include "necomd.mm"
include "simpllr.mm"
include "btwnlng1.mm"
include "lncom.mm"
include "tglinethru.mm"
include "eleqtrrd.mm"
include "pm2.61dane.mm"
include "wn.mm"
include "oppne1.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "mirmir.mm"
include "eqeltrrd.mm"
include "mtand.mm"
include "mirbtwn.mm"
include "islnoppd.mm"
include "eqidd.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "oppne2.mm"
include "eqcomd.mm"
include "mircom.mm"
include "mirbtwni.mm"
include "opphllem1.mm"
include "oppcom.mm"
include "mpjaodan.mm"

theorem opphllem2
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let cK: class K
  let cN: class N
  let cV: class V
  assume hpg.p: |- P = ( Base ` G )
  assume hpg.d: |- .- = ( dist ` G )
  assume hpg.i: |- I = ( Itv ` G )
  assume hpg.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume opphl.l: |- L = ( LineG ` G )
  assume opphl.d: |- ( ph -> D e. ran L )
  assume opphl.g: |- ( ph -> G e. TarskiG )
  assume opphllem1.s: |- S = ( ( pInvG ` G ) ` M )
  assume opphllem1.a: |- ( ph -> A e. P )
  assume opphllem1.b: |- ( ph -> B e. P )
  assume opphllem1.c: |- ( ph -> C e. P )
  assume opphllem1.r: |- ( ph -> R e. D )
  assume opphllem1.o: |- ( ph -> A O C )
  assume opphllem1.m: |- ( ph -> M e. D )
  assume opphllem1.n: |- ( ph -> A = ( S ` C ) )
  assume opphllem1.x: |- ( ph -> A =/= R )
  assume opphllem1.y: |- ( ph -> B =/= R )
  assume opphllem2.z: |- ( ph -> ( A e. ( R I B ) \/ B e. ( R I A ) ) )

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
  disjoint M t
  disjoint O t
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
  disjoint K t
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
    cR
    cB
    cI
    co
    wcel
    #
    cB
    cC
    cO
    wbr
    cB
    cR
    cA
    cI
    co
    wcel
    #
    wph
    @0
    wa
    #
    vt
    cC
    cB
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
    cD
    cL
    crn
    wcel
    #
    @0
    opphl.d
    adantr
    #
    wph
    cG
    cstrkg
    wcel
    #
    @0
    opphl.g
    adantr
    #
    wph
    cC
    cP
    wcel
    #
    @0
    opphllem1.c
    adantr
    #
    wph
    cB
    cP
    wcel
    #
    @0
    opphllem1.b
    adantr
    #
    @2
    vt
    cB
    cS
    cfv
    #
    cC
    cB
    cD
    cP
    cR
    cS
    cfv
    #
    cS
    cG
    cI
    cL
    cM
    c.mi
    cO
    va
    vb
    hpg.p
    hpg.d
    hpg.i
    hpg.o
    opphl.l
    @4
    @6
    opphllem1.s
    @2
    cM
    cP
    cG
    cmir
    cfv
    #
    cG
    cI
    cL
    cS
    c.mi
    cB
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @13
    eqid
    #
    @6
    wph
    cM
    cP
    wcel
    #
    @0
    wph
    cD
    cP
    cG
    cI
    cL
    cM
    hpg.p
    opphl.l
    hpg.i
    opphl.g
    opphl.d
    opphllem1.m
    tglnpt
    #
    adantr
    #
    opphllem1.s
    @10
    mircl
    #
    @8
    @10
    @2
    cM
    cR
    cD
    cP
    @13
    cG
    cI
    cL
    cS
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @14
    @6
    opphllem1.s
    @4
    wph
    cM
    cD
    wcel
    #
    @0
    opphllem1.m
    adantr
    #
    wph
    cR
    cD
    wcel
    #
    @0
    opphllem1.r
    adantr
    mirln
    #
    @2
    vt
    @11
    cB
    cM
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
    @18
    @10
    @20
    @2
    @11
    cD
    wcel
    #
    cB
    cD
    wcel
    #
    @2
    @24
    cA
    cD
    wcel
    #
    @2
    @24
    wa
    #
    @25
    cA
    cB
    @26
    cA
    cB
    wceq
    #
    wa
    cA
    cB
    cD
    @26
    @27
    simpr
    @2
    @24
    @27
    simplr
    eqeltrd
    @26
    cA
    cB
    wne
    #
    wa
    #
    cA
    cB
    cR
    cL
    co
    cD
    @29
    cP
    cG
    cI
    cL
    cB
    cR
    cA
    hpg.p
    hpg.i
    opphl.l
    wph
    @5
    @0
    @24
    @28
    opphl.g
    ad3antrrr
    #
    wph
    @9
    @0
    @24
    @28
    opphllem1.b
    ad3antrrr
    #
    wph
    cR
    cP
    wcel
    #
    @0
    @24
    @28
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
    opphllem1.r
    tglnpt
    #
    ad3antrrr
    #
    wph
    cA
    cP
    wcel
    #
    @0
    @24
    @28
    opphllem1.a
    ad3antrrr
    #
    wph
    cB
    cR
    wne
    #
    @0
    @24
    @28
    opphllem1.y
    ad3antrrr
    #
    @29
    cP
    cG
    cI
    cL
    cR
    cB
    cA
    hpg.p
    hpg.i
    opphl.l
    @30
    @34
    @31
    @36
    @29
    cB
    cR
    @38
    necomd
    wph
    @0
    @24
    @28
    simpllr
    btwnlng1
    lncom
    @29
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
    @30
    @31
    @34
    @38
    @38
    wph
    @3
    @0
    @24
    @28
    opphl.d
    ad3antrrr
    @2
    @24
    @28
    simplr
    wph
    @21
    @0
    @24
    @28
    opphllem1.r
    ad3antrrr
    tglinethru
    eleqtrrd
    pm2.61dane
    wph
    @25
    wn
    @0
    @24
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
    opphllem1.a
    opphllem1.c
    opphllem1.o
    oppne1
    ad2antrr
    pm2.65da
    #
    @2
    @23
    wa
    #
    @11
    cS
    cfv
    cB
    cD
    @40
    cM
    cB
    cP
    @13
    cG
    cI
    cL
    cS
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @14
    @2
    @5
    @23
    @6
    adantr
    #
    @2
    @15
    @23
    @17
    adantr
    opphllem1.s
    @2
    @9
    @23
    @10
    adantr
    mirmir
    @40
    cM
    @11
    cD
    cP
    @13
    cG
    cI
    cL
    cS
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @14
    @41
    opphllem1.s
    @2
    @3
    @23
    @4
    adantr
    @2
    @19
    @23
    @20
    adantr
    @2
    @23
    simpr
    mirln
    eqeltrrd
    mtand
    #
    @39
    @2
    cM
    cB
    cP
    @13
    cG
    cI
    cL
    cS
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @14
    @6
    @17
    opphllem1.s
    @10
    mirbtwn
    islnoppd
    @20
    @2
    @11
    eqidd
    @2
    @12
    @11
    @2
    @12
    cD
    wcel
    #
    @23
    wn
    @12
    @11
    wne
    @22
    @42
    @12
    @11
    cD
    nelne2
    syl2anc
    necomd
    @2
    @12
    cC
    @2
    @43
    cC
    cD
    wcel
    wn
    #
    @12
    cC
    wne
    @22
    wph
    @44
    @0
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
    opphllem1.a
    opphllem1.c
    opphllem1.o
    oppne2
    adantr
    @12
    cC
    cD
    nelne2
    syl2anc
    necomd
    @2
    cA
    cS
    cfv
    #
    cC
    @12
    @11
    cI
    co
    wph
    @45
    cC
    wceq
    @0
    wph
    cM
    cC
    cA
    cP
    @13
    cG
    cI
    cL
    cS
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @14
    opphl.g
    @16
    opphllem1.s
    opphllem1.c
    wph
    cA
    cC
    cS
    cfv
    #
    opphllem1.n
    eqcomd
    mircom
    adantr
    @2
    cM
    cP
    @13
    cG
    cI
    cL
    cS
    c.mi
    cR
    cA
    cB
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @14
    @6
    @17
    opphllem1.s
    wph
    @32
    @0
    @33
    adantr
    wph
    @35
    @0
    opphllem1.a
    adantr
    @10
    wph
    @0
    simpr
    mirbtwni
    eqeltrrd
    opphllem1
    oppcom
    wph
    @1
    wa
    vt
    cA
    cB
    cC
    cD
    cP
    cR
    cS
    cG
    cI
    cL
    cM
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
    @3
    @1
    opphl.d
    adantr
    wph
    @5
    @1
    opphl.g
    adantr
    opphllem1.s
    wph
    @35
    @1
    opphllem1.a
    adantr
    wph
    @9
    @1
    opphllem1.b
    adantr
    wph
    @7
    @1
    opphllem1.c
    adantr
    wph
    @21
    @1
    opphllem1.r
    adantr
    wph
    cA
    cC
    cO
    wbr
    @1
    opphllem1.o
    adantr
    wph
    @19
    @1
    opphllem1.m
    adantr
    wph
    cA
    @46
    wceq
    @1
    opphllem1.n
    adantr
    wph
    cA
    cR
    wne
    @1
    opphllem1.x
    adantr
    wph
    @37
    @1
    opphllem1.y
    adantr
    wph
    @1
    simpr
    opphllem1
    opphllem2.z
    mpjaodan
end
