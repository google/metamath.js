include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "ccn.mm"
include "cvmcn.mm"
include "cnf.mm"
include "syl.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cvmcov.mm"
include "ex.mm"
include "wex.mm"
include "n0.mm"
include "cvmsn0.mm"
include "ad2antll.mm"
include "sylib.mm"
include "cres.mm"
include "ccnv.mm"
include "cuni.mm"
include "wss.mm"
include "simprlr.mm"
include "cvmsss.mm"
include "simprr.mm"
include "sseldd.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "wf1o.mm"
include "simpll.mm"
include "cvmsf1o.mm"
include "syl3anc.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "simprll.mm"
include "ffvelrnd.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "fvres.mm"
include "eqtr3d.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "syld.mm"
include "ralrimiv.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem cvmfolem
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cX: class X
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
  let cA: class A
  assume cvmcov.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmseu.1: |- B = U. C
  assume cvmfolem.2: |- X = U. J

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
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B t
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( F e. ( C CovMap J ) -> F : B -onto-> X )

  proof
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cB
    cX
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cX
    wral
    cB
    cX
    cF
    wfo
    @0
    cF
    cC
    cJ
    ccn
    co
    wcel
    @1
    cC
    cF
    cJ
    cvmcn
    cF
    cC
    cJ
    cB
    cX
    cvmseu.1
    cvmfolem.2
    cnf
    syl
    @0
    @6
    vx
    cX
    @0
    @2
    cX
    wcel
    #
    @2
    vz
    cv
    #
    wcel
    #
    @8
    cS
    cfv
    #
    c0
    wne
    #
    wa
    #
    vz
    cJ
    wrex
    #
    @6
    @0
    @7
    @13
    vz
    vv
    vu
    cC
    @2
    cS
    vk
    cF
    cJ
    cX
    vs
    cvmcov.1
    cvmfolem.2
    cvmcov
    ex
    @0
    @12
    @6
    vz
    cJ
    @0
    @8
    cJ
    wcel
    #
    wa
    #
    @9
    @11
    @6
    @11
    vw
    cv
    #
    @10
    wcel
    #
    vw
    wex
    @15
    @9
    wa
    #
    @6
    vw
    @10
    n0
    @18
    @17
    @6
    vw
    @15
    @9
    @17
    @6
    @15
    @9
    @17
    wa
    #
    wa
    #
    vt
    cv
    #
    @16
    wcel
    #
    vt
    wex
    #
    @6
    @20
    @16
    c0
    wne
    #
    @23
    @17
    @24
    @15
    @9
    vv
    vu
    cC
    cS
    @16
    @8
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsn0
    ad2antll
    vt
    @16
    n0
    sylib
    @20
    @22
    @6
    vt
    @15
    @19
    @22
    @6
    @15
    @19
    @22
    wa
    #
    wa
    #
    @2
    cF
    @21
    cres
    #
    ccnv
    #
    cfv
    #
    cB
    wcel
    @2
    @29
    cF
    cfv
    #
    wceq
    #
    @6
    @26
    @21
    cB
    @29
    @26
    @21
    cC
    cuni
    #
    cB
    @26
    @21
    cC
    wcel
    @21
    @32
    wss
    @26
    @16
    cC
    @21
    @26
    @17
    @16
    cC
    wss
    @15
    @9
    @17
    @22
    simprlr
    #
    vv
    vu
    cC
    cS
    @16
    @8
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsss
    syl
    @15
    @19
    @22
    simprr
    #
    sseldd
    @21
    cC
    elssuni
    syl
    cvmseu.1
    syl6sseqr
    @26
    @8
    @21
    @2
    @28
    @26
    @21
    @8
    @27
    wf1o
    #
    @8
    @21
    @28
    wf1o
    @8
    @21
    @28
    wf
    @26
    @0
    @17
    @22
    @35
    @0
    @14
    @25
    simpll
    @33
    @34
    vv
    vu
    @21
    cC
    cS
    @16
    @8
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsf1o
    syl3anc
    #
    @21
    @8
    @27
    f1ocnv
    @8
    @21
    @28
    f1of
    3syl
    @15
    @9
    @17
    @22
    simprll
    #
    ffvelrnd
    #
    sseldd
    @26
    @29
    @27
    cfv
    #
    @2
    @30
    @26
    @35
    @9
    @39
    @2
    wceq
    @36
    @37
    @21
    @8
    @2
    @27
    f1ocnvfv2
    syl2anc
    @26
    @29
    @21
    wcel
    @39
    @30
    wceq
    @38
    @29
    @21
    cF
    fvres
    syl
    eqtr3d
    @5
    @31
    vy
    @29
    cB
    @3
    @29
    wceq
    @4
    @30
    @2
    @3
    @29
    cF
    fveq2
    eqeq2d
    rspcev
    syl2anc
    expr
    exlimdv
    mpd
    expr
    exlimdv
    syl5bi
    expimpd
    rexlimdva
    syld
    ralrimiv
    vy
    vx
    cB
    cX
    cF
    dffo3
    sylanbrc
end
