include "cfv.mm"
include "cmir.mm"
include "eqid.mm"
include "mircl.mm"
include "wbr.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "islnopp.mm"
include "mpbid.mm"
include "simpld.mm"
include "tglnpt.mm"
include "cstrkg.mm"
include "hlne1.mm"
include "necomd.mm"
include "hlln.mm"
include "wne.mm"
include "wo.mm"
include "w3a.mm"
include "ishlg.mm"
include "simp2d.mm"
include "lnrot1.mm"
include "adantr.mm"
include "crn.mm"
include "simpr.mm"
include "tglinethru.mm"
include "eleqtrrd.mm"
include "mtand.mm"
include "mirmir.mm"
include "mirbtwn.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "btwnlng1.mm"
include "mirln.mm"
include "eqeltrrd.mm"
include "jca.mm"
include "eleq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqidd.mm"
include "opphllem3.mm"
include "hlcomd.mm"
include "hltr.mm"
include "simp1d.mm"
include "simp3d.mm"
include "opphllem2.mm"
include "oppcom.mm"

theorem opphllem4
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
  assume opphllem3.t: |- ( ph -> R =/= S )
  assume opphllem3.l: |- ( ph -> ( S .- C ) ( leG ` G ) ( R .- A ) )
  assume opphllem3.u: |- ( ph -> U e. P )
  assume opphllem3.v: |- ( ph -> ( N ` R ) = S )
  assume opphllem4.u: |- ( ph -> V e. P )
  assume opphllem4.1: |- ( ph -> U ( K ` R ) A )
  assume opphllem4.2: |- ( ph -> V ( K ` S ) C )

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
    opphl.d
    opphl.g
    opphllem4.u
    opphllem3.u
    wph
    vt
    cU
    cN
    cfv
    #
    cV
    cU
    cD
    cP
    cS
    cN
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
    opphl.d
    opphl.g
    opphllem5.n
    wph
    cM
    cP
    cG
    cmir
    cfv
    #
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
    @1
    eqid
    #
    opphl.g
    opphllem5.m
    opphllem5.n
    opphllem3.u
    mircl
    #
    opphllem4.u
    opphllem3.u
    opphllem5.s
    wph
    @0
    cU
    cO
    wbr
    @0
    cD
    wcel
    #
    wn
    #
    cU
    cD
    wcel
    #
    wn
    #
    wa
    #
    vt
    cv
    #
    @0
    cU
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
    wph
    @8
    @12
    wph
    @5
    @7
    wph
    @4
    @6
    wph
    @6
    cA
    cD
    wcel
    #
    wph
    @13
    wn
    #
    cC
    cD
    wcel
    wn
    #
    wph
    @14
    @15
    wa
    #
    @9
    cA
    cC
    cI
    co
    wcel
    vt
    cD
    wrex
    #
    wph
    cA
    cC
    cO
    wbr
    @16
    @17
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
    simpld
    simpld
    wph
    @6
    wa
    #
    cA
    cR
    cU
    cL
    co
    #
    cD
    wph
    cA
    @19
    wcel
    @6
    wph
    cP
    cG
    cI
    cL
    cR
    cU
    cA
    hpg.p
    hpg.i
    opphl.l
    opphl.g
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
    opphllem3.u
    opphllem5.a
    wph
    cU
    cR
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
    opphllem3.u
    opphllem5.a
    @20
    opphl.g
    opphllem4.1
    hlne1
    necomd
    #
    wph
    cU
    cA
    cR
    cP
    cG
    cI
    cK
    cL
    hpg.p
    hpg.i
    opphl.k
    opphllem3.u
    opphllem5.a
    @20
    opphl.g
    opphl.l
    opphllem4.1
    hlln
    wph
    cU
    cR
    wne
    #
    cA
    cR
    wne
    #
    cU
    cR
    cA
    cI
    co
    wcel
    cA
    cR
    cU
    cI
    co
    wcel
    wo
    #
    wph
    cU
    cA
    cR
    cK
    cfv
    wbr
    #
    @22
    @23
    @24
    w3a
    opphllem4.1
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
    opphllem3.u
    opphllem5.a
    @20
    opphl.g
    ishlg
    mpbid
    simp2d
    lnrot1
    adantr
    @18
    cD
    cP
    cR
    cU
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
    @6
    opphl.g
    adantr
    wph
    cR
    cP
    wcel
    @6
    @20
    adantr
    wph
    cU
    cP
    wcel
    #
    @6
    opphllem3.u
    adantr
    wph
    cR
    cU
    wne
    @6
    @21
    adantr
    #
    @28
    wph
    cD
    cL
    crn
    wcel
    #
    @6
    opphl.d
    adantr
    wph
    cR
    cD
    wcel
    @6
    opphllem5.r
    adantr
    wph
    @6
    simpr
    tglinethru
    eleqtrrd
    mtand
    #
    wph
    @4
    wa
    #
    @0
    cN
    cfv
    cU
    cD
    @31
    cM
    cU
    cP
    @1
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @2
    wph
    @26
    @4
    opphl.g
    adantr
    #
    wph
    cM
    cP
    wcel
    @4
    opphllem5.m
    adantr
    opphllem5.n
    wph
    @27
    @4
    opphllem3.u
    adantr
    mirmir
    @31
    cM
    @0
    cD
    cP
    @1
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @2
    @32
    opphllem5.n
    wph
    @29
    @4
    opphl.d
    adantr
    wph
    cM
    cD
    wcel
    #
    @4
    wph
    cM
    cS
    cR
    cL
    co
    cD
    wph
    cP
    cG
    cI
    cL
    cS
    cR
    cM
    hpg.p
    hpg.i
    opphl.l
    opphl.g
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
    @20
    opphllem5.m
    wph
    cR
    cS
    opphllem3.t
    necomd
    #
    wph
    cM
    cR
    cN
    cfv
    #
    cR
    cI
    co
    cS
    cR
    cI
    co
    wph
    cM
    cR
    cP
    @1
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @2
    opphl.g
    opphllem5.m
    opphllem5.n
    @20
    mirbtwn
    wph
    @36
    cS
    cR
    cI
    opphllem3.v
    oveq1d
    eleqtrd
    btwnlng1
    wph
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
    opphl.g
    @34
    @20
    @35
    @35
    opphl.d
    opphllem5.s
    opphllem5.r
    tglinethru
    eleqtrrd
    #
    adantr
    wph
    @4
    simpr
    mirln
    eqeltrrd
    mtand
    @30
    jca
    wph
    @33
    cM
    @10
    wcel
    #
    @12
    @37
    wph
    cM
    cU
    cP
    @1
    cG
    cI
    cL
    cN
    c.mi
    hpg.p
    hpg.d
    hpg.i
    opphl.l
    @2
    opphl.g
    opphllem5.m
    opphllem5.n
    opphllem3.u
    mirbtwn
    @11
    @38
    vt
    cM
    cD
    @9
    cM
    @10
    eleq1
    rspcev
    syl2anc
    jca
    wph
    vt
    @0
    cU
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
    @3
    opphllem3.u
    islnopp
    mpbird
    @37
    wph
    @0
    eqidd
    wph
    @0
    cS
    wne
    #
    cV
    cS
    wne
    #
    @0
    cS
    cV
    cI
    co
    wcel
    cV
    cS
    @0
    cI
    co
    wcel
    wo
    #
    wph
    @0
    cV
    cS
    cK
    cfv
    #
    wbr
    @39
    @40
    @41
    w3a
    wph
    @0
    cC
    cV
    cS
    cP
    cG
    cI
    cK
    hpg.p
    hpg.i
    opphl.k
    @3
    opphllem5.c
    opphllem4.u
    opphl.g
    @34
    wph
    @25
    @0
    cC
    @42
    wbr
    opphllem4.1
    wph
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
    opphl.d
    opphl.g
    opphl.k
    opphllem5.n
    opphllem5.a
    opphllem5.c
    opphllem5.r
    opphllem5.s
    opphllem5.m
    opphllem5.o
    opphllem5.p
    opphllem5.q
    opphllem3.t
    opphllem3.l
    opphllem3.u
    opphllem3.v
    opphllem3
    mpbid
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
    opphllem4.u
    opphllem5.c
    @34
    opphl.g
    opphllem4.2
    hlcomd
    hltr
    wph
    @0
    cV
    cS
    cP
    cG
    cI
    cK
    cstrkg
    hpg.p
    hpg.i
    opphl.k
    @3
    opphllem4.u
    @34
    opphl.g
    ishlg
    mpbid
    #
    simp1d
    wph
    @39
    @40
    @41
    @43
    simp2d
    wph
    @39
    @40
    @41
    @43
    simp3d
    opphllem2
    oppcom
end
