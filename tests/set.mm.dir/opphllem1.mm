include "wbr.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wceq.mm"
include "simpr.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "tglnpt.mm"
include "necomd.mm"
include "btwnlng3.mm"
include "lncom.mm"
include "crn.mm"
include "tglinethru.mm"
include "eleqtrrd.mm"
include "pm2.61dane.mm"
include "oppne1.mm"
include "adantr.mm"
include "pm2.65da.mm"
include "oppne2.mm"
include "cfv.mm"
include "cmir.mm"
include "eqid.mm"
include "mirbtwn.mm"
include "eqcomd.mm"
include "mircom.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "axtgpasch.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprd.mm"
include "axtgbtwnid.mm"
include "eqeltrrd.mm"
include "adantlr.mm"
include "btwnlng1.mm"
include "simprrl.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "jca31.mm"
include "islnopp.mm"
include "mpbird.mm"

theorem opphllem1
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
  assume opphllem1.z: |- ( ph -> B e. ( R I A ) )

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
    cB
    cC
    cO
    wbr
    cB
    cD
    wcel
    #
    wn
    #
    cC
    cD
    wcel
    wn
    #
    wa
    vt
    cv
    #
    cB
    cC
    cI
    co
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    wph
    @1
    @2
    @5
    wph
    @0
    cA
    cD
    wcel
    #
    wph
    @0
    wa
    #
    @6
    cA
    cB
    @7
    cA
    cB
    wceq
    #
    wa
    cA
    cB
    cD
    @7
    @8
    simpr
    wph
    @0
    @8
    simplr
    eqeltrd
    @7
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
    @10
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
    cG
    cstrkg
    wcel
    #
    @0
    @9
    opphl.g
    ad2antrr
    #
    wph
    cB
    cP
    wcel
    @0
    @9
    opphllem1.b
    ad2antrr
    #
    wph
    cR
    cP
    wcel
    #
    @0
    @9
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
    ad2antrr
    #
    wph
    cA
    cP
    wcel
    @0
    @9
    opphllem1.a
    ad2antrr
    #
    wph
    cB
    cR
    wne
    @0
    @9
    opphllem1.y
    ad2antrr
    #
    @10
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
    @12
    @16
    @13
    @17
    @10
    cB
    cR
    @18
    necomd
    wph
    cB
    cR
    cA
    cI
    co
    wcel
    @0
    @9
    opphllem1.z
    ad2antrr
    btwnlng3
    lncom
    @10
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
    @12
    @13
    @16
    @18
    @18
    wph
    cD
    cL
    crn
    wcel
    #
    @0
    @9
    opphl.d
    ad2antrr
    wph
    @0
    @9
    simplr
    wph
    cR
    cD
    wcel
    #
    @0
    @9
    opphllem1.r
    ad2antrr
    tglinethru
    eleqtrrd
    pm2.61dane
    wph
    @6
    wn
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
    oppne1
    adantr
    pm2.65da
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
    wph
    @4
    @3
    cM
    cR
    cI
    co
    #
    wcel
    #
    wa
    #
    vt
    cP
    wrex
    @5
    wph
    cP
    cB
    cG
    cI
    c.mi
    cM
    cR
    cC
    cA
    vt
    hpg.p
    hpg.d
    hpg.i
    opphl.g
    @15
    opphllem1.c
    opphllem1.a
    opphllem1.b
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
    opphllem1.z
    wph
    cM
    cA
    cS
    cfv
    #
    cA
    cI
    co
    cC
    cA
    cI
    co
    wph
    cM
    cA
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
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @26
    eqid
    #
    opphl.g
    @24
    opphllem1.s
    opphllem1.a
    mirbtwn
    wph
    @25
    cC
    cA
    cI
    wph
    cM
    cC
    cA
    cP
    @26
    cG
    cI
    cL
    cS
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @27
    opphl.g
    @24
    opphllem1.s
    opphllem1.c
    wph
    cA
    cC
    cS
    cfv
    opphllem1.n
    eqcomd
    mircom
    oveq1d
    eleqtrd
    axtgpasch
    wph
    @23
    @4
    vt
    cP
    cD
    wph
    @3
    cP
    wcel
    #
    @23
    wa
    #
    @3
    cD
    wcel
    #
    @4
    wa
    wph
    @29
    wa
    #
    @30
    @4
    @31
    @30
    cM
    cR
    @31
    cM
    cR
    wceq
    #
    wa
    #
    cR
    @3
    cD
    @33
    cP
    cG
    cI
    c.mi
    cR
    @3
    hpg.p
    hpg.d
    hpg.i
    wph
    @11
    @29
    @32
    opphl.g
    ad2antrr
    wph
    @14
    @29
    @32
    @15
    ad2antrr
    wph
    @28
    @23
    @32
    simplrl
    @33
    @3
    @21
    cR
    cR
    cI
    co
    @33
    @4
    @22
    wph
    @28
    @23
    @32
    simplrr
    simprd
    @33
    cM
    cR
    cR
    cI
    @31
    @32
    simpr
    oveq1d
    eleqtrd
    axtgbtwnid
    wph
    @20
    @29
    @32
    opphllem1.r
    ad2antrr
    eqeltrrd
    @31
    cM
    cR
    wne
    #
    wa
    #
    @3
    cM
    cR
    cL
    co
    #
    cD
    @35
    cP
    cG
    cI
    cL
    cM
    cR
    @3
    hpg.p
    hpg.i
    opphl.l
    wph
    @34
    @11
    @29
    wph
    @11
    @34
    opphl.g
    adantr
    #
    adantlr
    wph
    @34
    cM
    cP
    wcel
    #
    @29
    wph
    @38
    @34
    @24
    adantr
    #
    adantlr
    wph
    @34
    @14
    @29
    wph
    @14
    @34
    @15
    adantr
    #
    adantlr
    wph
    @28
    @23
    @34
    simplrl
    @31
    @34
    simpr
    @35
    @4
    @22
    wph
    @28
    @23
    @34
    simplrr
    simprd
    btwnlng1
    wph
    @34
    cD
    @36
    wceq
    @29
    wph
    @34
    wa
    cD
    cP
    cM
    cR
    cG
    cI
    cL
    hpg.p
    hpg.i
    opphl.l
    @37
    @39
    @40
    wph
    @34
    simpr
    #
    @41
    wph
    @19
    @34
    opphl.d
    adantr
    wph
    cM
    cD
    wcel
    @34
    opphllem1.m
    adantr
    wph
    @20
    @34
    opphllem1.r
    adantr
    tglinethru
    adantlr
    eleqtrrd
    pm2.61dane
    wph
    @28
    @4
    @22
    simprrl
    jca
    ex
    reximdv2
    mpd
    jca31
    wph
    vt
    cB
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
    opphllem1.b
    opphllem1.c
    islnopp
    mpbird
end
