include "cv.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cres.mm"
include "crest.mm"
include "co.mm"
include "chmeo.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt.mm"
include "weq.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "ineq2.mm"
include "cbvralv.mm"
include "sneq.mm"
include "difeq2d.mm"
include "ineq1.mm"
include "raleqbidv.mm"
include "syl5bb.mm"
include "reseq2.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "difeq1.mm"
include "raleqdv.mm"
include "anbi1d.mm"
include "raleqbi1dv.mm"
include "cbvrabv.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "cbvmptv.mm"
include "eqtri.mm"

theorem cvmscbv
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let cX: class X
  assume iscvm.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint c d
  disjoint c k
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint d k
  disjoint d s
  disjoint d u
  disjoint d v
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint s u
  disjoint s v
  disjoint u v
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C k
  disjoint C s
  disjoint C u
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint J a
  disjoint J b
  disjoint J c
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint a f
  disjoint a j
  disjoint a x
  disjoint b f
  disjoint b j
  disjoint b x
  disjoint c f
  disjoint c j
  disjoint c x
  disjoint d f
  disjoint d j
  disjoint d x
  disjoint f j
  disjoint f k
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint j k
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint k x
  disjoint s x
  disjoint u x
  disjoint v x
  disjoint C f
  disjoint C j
  disjoint C x
  disjoint X c
  disjoint X f
  disjoint X j
  disjoint X x
  disjoint F f
  disjoint F x
  disjoint J f
  disjoint J j
  disjoint J x
  assert |- S = ( a e. J |-> { b e. ( ~P C \ { (/) } ) | ( U. b = ( `' F " a ) /\ A. c e. b ( A. d e. ( b \ { c } ) ( c i^i d ) = (/) /\ ( F |` c ) e. ( ( C |`t c ) Homeo ( J |`t a ) ) ) ) } )

  proof
    cS
    vk
    cJ
    vs
    cv
    #
    cuni
    #
    cF
    ccnv
    #
    vk
    cv
    #
    cima
    #
    wceq
    #
    vu
    cv
    #
    vv
    cv
    #
    cin
    #
    c0
    wceq
    #
    vv
    @0
    @6
    csn
    #
    cdif
    #
    wral
    #
    cF
    @6
    cres
    #
    cC
    @6
    crest
    co
    #
    cJ
    @3
    crest
    co
    #
    chmeo
    co
    #
    wcel
    #
    wa
    #
    vu
    @0
    wral
    #
    wa
    #
    vs
    cC
    cpw
    c0
    csn
    cdif
    #
    crab
    #
    cmpt
    va
    cJ
    vb
    cv
    #
    cuni
    #
    @2
    va
    cv
    #
    cima
    #
    wceq
    #
    vc
    cv
    #
    vd
    cv
    #
    cin
    #
    c0
    wceq
    #
    vd
    @23
    @28
    csn
    #
    cdif
    #
    wral
    #
    cF
    @28
    cres
    #
    cC
    @28
    crest
    co
    #
    cJ
    @25
    crest
    co
    #
    chmeo
    co
    #
    wcel
    #
    wa
    #
    vc
    @23
    wral
    #
    wa
    #
    vb
    @21
    crab
    #
    cmpt
    iscvm.1
    vk
    va
    cJ
    @22
    @43
    vk
    va
    weq
    #
    @22
    @24
    @4
    wceq
    #
    @34
    @35
    @36
    @15
    chmeo
    co
    #
    wcel
    #
    wa
    #
    vc
    @23
    wral
    #
    wa
    #
    vb
    @21
    crab
    @43
    @20
    @50
    vs
    vb
    @21
    vs
    vb
    weq
    #
    @5
    @45
    @19
    @49
    @51
    @1
    @24
    @4
    @0
    @23
    unieq
    eqeq1d
    @19
    @31
    vd
    @0
    @32
    cdif
    #
    wral
    #
    @47
    wa
    #
    vc
    @0
    wral
    @51
    @49
    @18
    @54
    vu
    vc
    @0
    vu
    vc
    weq
    #
    @12
    @53
    @17
    @47
    @12
    @6
    @29
    cin
    #
    c0
    wceq
    #
    vd
    @11
    wral
    @55
    @53
    @9
    @57
    vv
    vd
    @11
    vv
    vd
    weq
    @8
    @56
    c0
    @7
    @29
    @6
    ineq2
    eqeq1d
    cbvralv
    @55
    @57
    @31
    vd
    @11
    @52
    @55
    @10
    @32
    @0
    @6
    @28
    sneq
    difeq2d
    @55
    @56
    @30
    c0
    @6
    @28
    @29
    ineq1
    eqeq1d
    raleqbidv
    syl5bb
    @55
    @13
    @35
    @16
    @46
    @6
    @28
    cF
    reseq2
    @55
    @14
    @36
    @15
    chmeo
    @6
    @28
    cC
    crest
    oveq2
    oveq1d
    eleq12d
    anbi12d
    cbvralv
    @54
    @48
    vc
    @0
    @23
    @51
    @53
    @34
    @47
    @51
    @31
    vd
    @52
    @33
    @0
    @23
    @32
    difeq1
    raleqdv
    anbi1d
    raleqbi1dv
    syl5bb
    anbi12d
    cbvrabv
    @44
    @50
    @42
    vb
    @21
    @44
    @45
    @27
    @49
    @41
    @44
    @4
    @26
    @24
    @3
    @25
    @2
    imaeq2
    eqeq2d
    @44
    @48
    @40
    vc
    @23
    @44
    @47
    @39
    @34
    @44
    @46
    @38
    @35
    @44
    @15
    @37
    @36
    chmeo
    @3
    @25
    cJ
    crest
    oveq2
    oveq2d
    eleq2d
    anbi2d
    ralbidv
    anbi12d
    rabbidv
    syl5eq
    cbvmptv
    eqtri
end
