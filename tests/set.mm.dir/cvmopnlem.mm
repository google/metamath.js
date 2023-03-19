include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cima.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "simpll.mm"
include "wf.mm"
include "ccn.mm"
include "cvmcn.mm"
include "adantr.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "adantl.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "cvmcov.mm"
include "syl2anc.mm"
include "wex.mm"
include "n0.mm"
include "crio.mm"
include "cin.mm"
include "crest.mm"
include "cres.mm"
include "wceq.mm"
include "inss2.mm"
include "resima2.mm"
include "ax-mp.mm"
include "chmeo.mm"
include "simprr.mm"
include "simprl.mm"
include "cvmsiota.mm"
include "syl13anc.mm"
include "simpld.mm"
include "cvmshmeo.mm"
include "ctop.mm"
include "cvmtop1.mm"
include "simpllr.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "hmeoima.mm"
include "syl5eqelr.mm"
include "wb.mm"
include "cvmtop2.mm"
include "ad2antrr.mm"
include "cvmsrcl.mm"
include "ad2antll.mm"
include "restopn2.mm"
include "mpbid.mm"
include "wfn.mm"
include "ffn.mm"
include "inss1.mm"
include "syl5ss.mm"
include "simplr.mm"
include "simprd.mm"
include "elind.mm"
include "fnfvima.mm"
include "imass2.mm"
include "mp1i.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "expr.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "rexlimdvw.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "ralima.mm"
include "mpbird.mm"
include "eltop2.mm"

theorem cvmopnlem
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cT: class T
  let cV: class V
  let cW: class W
  let cX: class X
  assume cvmcov.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmseu.1: |- B = U. C

  disjoint k s
  disjoint k u
  disjoint k v
  disjoint C k
  disjoint s u
  disjoint s v
  disjoint C s
  disjoint u v
  disjoint C u
  disjoint C v
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint A u
  disjoint A v
  disjoint B v
  disjoint a b
  disjoint a k
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b k
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint C t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint J a
  disjoint J b
  disjoint J t
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint S t
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint U k
  disjoint U s
  disjoint U t
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint T z
  disjoint V a
  disjoint V b
  disjoint V k
  disjoint V s
  disjoint V t
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A t
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B t
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( ( F e. ( C CovMap J ) /\ A e. C ) -> ( F " A ) e. J )

  proof
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cA
    cC
    wcel
    #
    wa
    #
    cF
    cA
    cima
    #
    cJ
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @6
    @3
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    vx
    @3
    wral
    #
    @2
    @11
    vz
    cv
    #
    cF
    cfv
    #
    @6
    wcel
    #
    @8
    wa
    #
    vy
    cJ
    wrex
    #
    vz
    cA
    wral
    #
    @2
    @16
    vz
    cA
    @2
    @12
    cA
    wcel
    #
    wa
    #
    @13
    vt
    cv
    #
    wcel
    #
    @20
    cS
    cfv
    #
    c0
    wne
    #
    wa
    #
    vt
    cJ
    wrex
    #
    @16
    @19
    @0
    @13
    cJ
    cuni
    #
    wcel
    @25
    @0
    @1
    @18
    simpll
    #
    @19
    cB
    @26
    @12
    cF
    @2
    cB
    @26
    cF
    wf
    #
    @18
    @2
    cF
    cC
    cJ
    ccn
    co
    wcel
    #
    @28
    @0
    @29
    @1
    cC
    cF
    cJ
    cvmcn
    adantr
    cF
    cC
    cJ
    cB
    @26
    cvmseu.1
    @26
    eqid
    #
    cnf
    syl
    #
    adantr
    @2
    cA
    cB
    @12
    @1
    cA
    cB
    wss
    #
    @0
    @1
    cA
    cC
    cuni
    cB
    cA
    cC
    elssuni
    cvmseu.1
    syl6sseqr
    #
    adantl
    #
    sselda
    #
    ffvelrnd
    vt
    vv
    vu
    cC
    @13
    cS
    vk
    cF
    cJ
    @26
    vs
    cvmcov.1
    @30
    cvmcov
    syl2anc
    @19
    @24
    @16
    vt
    cJ
    @19
    @21
    @23
    @16
    @23
    vw
    cv
    #
    @22
    wcel
    #
    vw
    wex
    @19
    @21
    wa
    #
    @16
    vw
    @22
    n0
    @38
    @37
    @16
    vw
    @19
    @21
    @37
    @16
    @19
    @21
    @37
    wa
    #
    wa
    #
    cF
    cA
    @12
    @5
    wcel
    vx
    @36
    crio
    #
    cin
    #
    cima
    #
    cJ
    wcel
    #
    @13
    @43
    wcel
    #
    @43
    @3
    wss
    #
    @16
    @40
    @44
    @43
    @20
    wss
    #
    @40
    @43
    cJ
    @20
    crest
    co
    #
    wcel
    #
    @44
    @47
    wa
    #
    @40
    @43
    cF
    @41
    cres
    #
    @42
    cima
    #
    @48
    @42
    @41
    wss
    @52
    @43
    wceq
    cA
    @41
    inss2
    cF
    @42
    @41
    resima2
    ax-mp
    @40
    @51
    cC
    @41
    crest
    co
    #
    @48
    chmeo
    co
    wcel
    #
    @42
    @53
    wcel
    #
    @52
    @48
    wcel
    @40
    @37
    @41
    @36
    wcel
    #
    @54
    @19
    @21
    @37
    simprr
    #
    @40
    @56
    @12
    @41
    wcel
    #
    @40
    @0
    @37
    @12
    cB
    wcel
    #
    @21
    @56
    @58
    wa
    @19
    @0
    @39
    @27
    adantr
    #
    @57
    @19
    @59
    @39
    @35
    adantr
    @19
    @21
    @37
    simprl
    vx
    vv
    vu
    @12
    cB
    cC
    cS
    @36
    @20
    vk
    cF
    cJ
    @41
    vs
    cvmcov.1
    cvmseu.1
    @41
    eqid
    cvmsiota
    syl13anc
    #
    simpld
    #
    vv
    vu
    @41
    cC
    cS
    @36
    @20
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmshmeo
    syl2anc
    @40
    cC
    ctop
    wcel
    #
    @56
    @1
    @55
    @40
    @0
    @63
    @60
    cC
    cF
    cJ
    cvmtop1
    syl
    @62
    @0
    @1
    @18
    @39
    simpllr
    #
    cA
    @41
    cC
    ctop
    @36
    elrestr
    syl3anc
    @42
    @51
    @53
    @48
    hmeoima
    syl2anc
    syl5eqelr
    @40
    cJ
    ctop
    wcel
    #
    @20
    cJ
    wcel
    #
    @49
    @50
    wb
    @2
    @65
    @18
    @39
    @0
    @65
    @1
    cC
    cF
    cJ
    cvmtop2
    adantr
    #
    ad2antrr
    @37
    @66
    @19
    @21
    vv
    vu
    cC
    cS
    @36
    @20
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsrcl
    ad2antll
    @20
    @43
    cJ
    restopn2
    syl2anc
    mpbid
    simpld
    @40
    cF
    cB
    wfn
    #
    @42
    cB
    wss
    @12
    @42
    wcel
    @45
    @2
    @68
    @18
    @39
    @2
    @28
    @68
    @31
    cB
    @26
    cF
    ffn
    syl
    #
    ad2antrr
    @40
    @42
    cA
    cB
    cA
    @41
    inss1
    #
    @40
    @1
    @32
    @64
    @33
    syl
    syl5ss
    @40
    cA
    @41
    @12
    @2
    @18
    @39
    simplr
    @40
    @56
    @58
    @61
    simprd
    elind
    cB
    @42
    cF
    @12
    fnfvima
    syl3anc
    @42
    cA
    wss
    @46
    @40
    @70
    @42
    cA
    cF
    imass2
    mp1i
    @15
    @45
    @46
    wa
    vy
    @43
    cJ
    @6
    @43
    wceq
    @14
    @45
    @8
    @46
    @6
    @43
    @13
    eleq2
    @6
    @43
    @3
    sseq1
    anbi12d
    rspcev
    syl12anc
    expr
    exlimdv
    syl5bi
    expimpd
    rexlimdvw
    mpd
    ralrimiva
    @2
    @68
    @32
    @11
    @17
    wb
    @69
    @34
    @10
    @16
    vx
    vz
    cB
    cA
    cF
    @5
    @13
    wceq
    #
    @9
    @15
    vy
    cJ
    @71
    @7
    @14
    @8
    @5
    @13
    @6
    eleq1
    anbi1d
    rexbidv
    ralima
    syl2anc
    mpbird
    @2
    @65
    @4
    @11
    wb
    @67
    vx
    vy
    @3
    cJ
    eltop2
    syl
    mpbird
end
