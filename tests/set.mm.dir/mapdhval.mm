include "cotp.mm"
include "cfv.mm"
include "c2nd.mm"
include "wceq.mm"
include "csn.mm"
include "cv.mm"
include "c1st.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "cvv.mm"
include "wcel.mm"
include "otex.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "riotabidv.mm"
include "ifbieq2d.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "riotaex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "mp1i.mm"
include "ot3rdg.mm"
include "syl.mm"
include "ot1stg.mm"
include "syl3anc.mm"
include "ot2ndg.mm"
include "eqtrd.mm"

theorem mapdhval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume mapdh.q: |- Q = ( 0g ` C )
  assume mapdh.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh.x: |- ( ph -> X e. A )
  assume mapdh.f: |- ( ph -> F e. B )
  assume mapdh.y: |- ( ph -> Y e. E )

  disjoint D x
  disjoint h x
  disjoint F h
  disjoint F x
  disjoint J x
  disjoint M x
  disjoint N x
  disjoint .0. x
  disjoint Q x
  disjoint R x
  disjoint .- x
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint h ph
  assert |- ( ph -> ( I ` <. X , F , Y >. ) = if ( Y = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { Y } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( F R h ) } ) ) ) ) )

  proof
    wph
    cX
    cF
    cY
    cotp
    #
    cI
    cfv
    #
    @0
    c2nd
    cfv
    #
    c.0
    wceq
    #
    cQ
    @2
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    vh
    cv
    #
    csn
    cJ
    cfv
    #
    wceq
    #
    @0
    c1st
    cfv
    #
    c1st
    cfv
    #
    @2
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    @10
    c2nd
    cfv
    #
    @7
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    wa
    #
    vh
    cD
    crio
    #
    cif
    #
    cY
    c.0
    wceq
    #
    cQ
    cY
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    @8
    wceq
    #
    cX
    cY
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    cF
    @7
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    wa
    #
    vh
    cD
    crio
    #
    cif
    @0
    cvv
    wcel
    @1
    @23
    wceq
    wph
    cX
    cF
    cY
    otex
    vx
    @0
    vx
    cv
    #
    c2nd
    cfv
    #
    c.0
    wceq
    #
    cQ
    @40
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    @8
    wceq
    #
    @39
    c1st
    cfv
    #
    c1st
    cfv
    #
    @40
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    @46
    c2nd
    cfv
    #
    @7
    cR
    co
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    wa
    #
    vh
    cD
    crio
    #
    cif
    @23
    cvv
    cI
    @39
    @0
    wceq
    #
    @41
    @3
    @58
    @22
    cQ
    @59
    @40
    @2
    c.0
    @39
    @0
    c2nd
    fveq2
    #
    eqeq1d
    @59
    @57
    @21
    vh
    cD
    @59
    @45
    @9
    @56
    @20
    @59
    @44
    @6
    @8
    @59
    @43
    @5
    cM
    @59
    @42
    @4
    cN
    @59
    @40
    @2
    @60
    sneqd
    fveq2d
    fveq2d
    eqeq1d
    @59
    @51
    @15
    @55
    @19
    @59
    @50
    @14
    cM
    @59
    @49
    @13
    cN
    @59
    @48
    @12
    @59
    @47
    @11
    @40
    @2
    c.mi
    @59
    @46
    @10
    c1st
    @39
    @0
    c1st
    fveq2
    #
    fveq2d
    @60
    oveq12d
    sneqd
    fveq2d
    fveq2d
    @59
    @54
    @18
    cJ
    @59
    @53
    @17
    @59
    @52
    @16
    @7
    cR
    @59
    @46
    @10
    c2nd
    @61
    fveq2d
    oveq1d
    sneqd
    fveq2d
    eqeq12d
    anbi12d
    riotabidv
    ifbieq2d
    mapdh.i
    @3
    cQ
    @22
    cQ
    cC
    c0g
    cfv
    cvv
    mapdh.q
    cC
    c0g
    fvex
    eqeltri
    @21
    vh
    cD
    riotaex
    ifex
    fvmpt
    mp1i
    wph
    @3
    @24
    @22
    @38
    cQ
    wph
    @2
    cY
    c.0
    wph
    cY
    cE
    wcel
    #
    @2
    cY
    wceq
    mapdh.y
    cX
    cF
    cY
    cE
    ot3rdg
    syl
    #
    eqeq1d
    wph
    @21
    @37
    vh
    cD
    wph
    @9
    @28
    @20
    @36
    wph
    @6
    @27
    @8
    wph
    @5
    @26
    cM
    wph
    @4
    @25
    cN
    wph
    @2
    cY
    @63
    sneqd
    fveq2d
    fveq2d
    eqeq1d
    wph
    @15
    @32
    @19
    @35
    wph
    @14
    @31
    cM
    wph
    @13
    @30
    cN
    wph
    @12
    @29
    wph
    @11
    cX
    @2
    cY
    c.mi
    wph
    cX
    cA
    wcel
    #
    cF
    cB
    wcel
    #
    @62
    @11
    cX
    wceq
    mapdh.x
    mapdh.f
    mapdh.y
    cX
    cF
    cY
    cA
    cB
    cE
    ot1stg
    syl3anc
    @63
    oveq12d
    sneqd
    fveq2d
    fveq2d
    wph
    @18
    @34
    cJ
    wph
    @17
    @33
    wph
    @16
    cF
    @7
    cR
    wph
    @64
    @65
    @62
    @16
    cF
    wceq
    mapdh.x
    mapdh.f
    mapdh.y
    cX
    cF
    cY
    cA
    cB
    cE
    ot2ndg
    syl3anc
    oveq1d
    sneqd
    fveq2d
    eqeq12d
    anbi12d
    riotabidv
    ifbieq2d
    eqtrd
end
