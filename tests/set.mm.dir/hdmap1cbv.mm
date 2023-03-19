include "cvv.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "c1st.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "weq.mm"
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
include "cbvmptv.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "cbvriotav.mm"
include "ifeq2.mm"
include "ax-mp.mm"
include "mpteq2i.mm"
include "3eqtri.mm"

theorem hdmap1cbv
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cQ: class Q
  let cR: class R
  let vh: setvar h
  let vi: setvar i
  let cJ: class J
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let c.0: class .0.
  assume hdmap1cbv.l: |- L = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )

  disjoint h i
  disjoint h x
  disjoint h y
  disjoint D h
  disjoint i x
  disjoint i y
  disjoint D i
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint J h
  disjoint J i
  disjoint J x
  disjoint J y
  disjoint M h
  disjoint M i
  disjoint M x
  disjoint M y
  disjoint N h
  disjoint N i
  disjoint N x
  disjoint N y
  disjoint .0. x
  disjoint .0. y
  disjoint Q x
  disjoint Q y
  disjoint R h
  disjoint R i
  disjoint R x
  disjoint R y
  disjoint .- h
  disjoint .- i
  disjoint .- x
  disjoint .- y
  assert |- L = ( y e. _V |-> if ( ( 2nd ` y ) = .0. , Q , ( iota_ i e. D ( ( M ` ( N ` { ( 2nd ` y ) } ) ) = ( J ` { i } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` y ) ) .- ( 2nd ` y ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` y ) ) R i ) } ) ) ) ) )

  proof
    cL
    vx
    cvv
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
    @1
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
    #
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
    @1
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
    @6
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
    cmpt
    vy
    cvv
    vy
    cv
    #
    c2nd
    cfv
    #
    c.0
    wceq
    #
    cQ
    @25
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
    @24
    c1st
    cfv
    #
    c1st
    cfv
    #
    @25
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
    @31
    c2nd
    cfv
    #
    @6
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
    cmpt
    vy
    cvv
    @26
    cQ
    @29
    vi
    cv
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    @36
    @37
    @45
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
    vi
    cD
    crio
    #
    cif
    #
    cmpt
    hdmap1cbv.l
    vx
    vy
    cvv
    @23
    @44
    vx
    vy
    weq
    #
    @2
    @26
    @22
    @43
    cQ
    @56
    @1
    @25
    c.0
    @0
    @24
    c2nd
    fveq2
    #
    eqeq1d
    @56
    @21
    @42
    vh
    cD
    @56
    @9
    @30
    @20
    @41
    @56
    @5
    @29
    @8
    @56
    @4
    @28
    cM
    @56
    @3
    @27
    cN
    @56
    @1
    @25
    @57
    sneqd
    fveq2d
    fveq2d
    eqeq1d
    @56
    @15
    @36
    @19
    @40
    @56
    @14
    @35
    cM
    @56
    @13
    @34
    cN
    @56
    @12
    @33
    @56
    @11
    @32
    @1
    @25
    c.mi
    @56
    @10
    @31
    c1st
    @0
    @24
    c1st
    fveq2
    #
    fveq2d
    @57
    oveq12d
    sneqd
    fveq2d
    fveq2d
    @56
    @18
    @39
    cJ
    @56
    @17
    @38
    @56
    @16
    @37
    @6
    cR
    @56
    @10
    @31
    c2nd
    @58
    fveq2d
    oveq1d
    sneqd
    fveq2d
    eqeq12d
    anbi12d
    riotabidv
    ifbieq2d
    cbvmptv
    vy
    cvv
    @44
    @55
    @43
    @54
    wceq
    @44
    @55
    wceq
    @42
    @53
    vh
    vi
    cD
    vh
    vi
    weq
    #
    @30
    @48
    @41
    @52
    @59
    @8
    @47
    @29
    @59
    @7
    @46
    cJ
    @6
    @45
    sneq
    fveq2d
    eqeq2d
    @59
    @40
    @51
    @36
    @59
    @39
    @50
    cJ
    @59
    @38
    @49
    @6
    @45
    @37
    cR
    oveq2
    sneqd
    fveq2d
    eqeq2d
    anbi12d
    cbvriotav
    @26
    @43
    @54
    cQ
    ifeq2
    ax-mp
    mpteq2i
    3eqtri
end
