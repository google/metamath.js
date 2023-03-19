include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "ccvm.mm"
include "anass.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "cin.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "crest.mm"
include "chmeo.mm"
include "cpw.mm"
include "crab.mm"
include "df-cvm.mm"
include "elmpt2cl.mm"
include "oveq12.mm"
include "simpr.mm"
include "unieqd.mm"
include "syl6eqr.mm"
include "simpl.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "oveq1.mm"
include "oveqan12d.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "ralbidv.mm"
include "rexeqbidv.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "cvv.mm"
include "id.mm"
include "pwexg.mm"
include "adantr.mm"
include "difexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "fvmpt2.mm"
include "syl2anr.mm"
include "neeq1d.mm"
include "rabn0.mm"
include "syl6bb.mm"
include "rexbidva.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eqeq2d.mm"
include "reseq1.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "syl6bbr.mm"
include "bitr4d.mm"
include "biadan2.mm"
include "3bitr4ri.mm"

theorem iscvm
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vj: setvar j
  assume iscvm.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume iscvm.2: |- X = U. J

  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint C k
  disjoint C s
  disjoint C u
  disjoint C x
  disjoint X x
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint F x
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a j
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b j
  disjoint b k
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint c d
  disjoint c f
  disjoint c j
  disjoint c k
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint d f
  disjoint d j
  disjoint d k
  disjoint d s
  disjoint d u
  disjoint d v
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
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C f
  disjoint C j
  disjoint X c
  disjoint X f
  disjoint X j
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F f
  disjoint J a
  disjoint J b
  disjoint J c
  disjoint J f
  disjoint J j
  assert |- ( F e. ( C CovMap J ) <-> ( ( C e. Top /\ J e. Top /\ F e. ( C Cn J ) ) /\ A. x e. X E. k e. J ( x e. k /\ ( S ` k ) =/= (/) ) ) )

  proof
    cC
    ctop
    wcel
    #
    cJ
    ctop
    wcel
    #
    wa
    #
    cF
    cC
    cJ
    ccn
    co
    #
    wcel
    #
    wa
    #
    vx
    cv
    vk
    cv
    #
    wcel
    #
    @6
    cS
    cfv
    #
    c0
    wne
    #
    wa
    #
    vk
    cJ
    wrex
    #
    vx
    cX
    wral
    #
    wa
    @2
    @4
    @12
    wa
    #
    wa
    @0
    @1
    @4
    w3a
    #
    @12
    wa
    cF
    cC
    cJ
    ccvm
    co
    #
    wcel
    #
    @2
    @4
    @12
    anass
    @14
    @5
    @12
    @0
    @1
    @4
    df-3an
    anbi1i
    @16
    @2
    @13
    vc
    vj
    ctop
    ctop
    @7
    vs
    cv
    #
    cuni
    #
    vf
    cv
    #
    ccnv
    #
    @6
    cima
    #
    wceq
    #
    vu
    cv
    #
    vv
    cv
    cin
    c0
    wceq
    vv
    @17
    @23
    csn
    cdif
    wral
    #
    @19
    @23
    cres
    #
    vc
    cv
    #
    @23
    crest
    co
    #
    vj
    cv
    #
    @6
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
    @17
    wral
    #
    wa
    #
    vs
    @26
    cpw
    #
    c0
    csn
    #
    cdif
    #
    wrex
    #
    wa
    #
    vk
    @28
    wrex
    #
    vx
    @28
    cuni
    #
    wral
    #
    vf
    @26
    @28
    ccn
    co
    #
    crab
    #
    cC
    cJ
    ccvm
    cF
    vx
    vv
    vu
    vf
    vj
    vk
    vs
    vc
    df-cvm
    #
    elmpt2cl
    @2
    @16
    cF
    @7
    @22
    @24
    @25
    cC
    @23
    crest
    co
    #
    cJ
    @6
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
    @17
    wral
    #
    wa
    #
    vs
    cC
    cpw
    #
    @36
    cdif
    #
    wrex
    #
    wa
    #
    vk
    cJ
    wrex
    #
    vx
    cX
    wral
    #
    vf
    @3
    crab
    #
    wcel
    #
    @13
    @2
    @15
    @59
    cF
    vc
    vj
    cC
    cJ
    ctop
    ctop
    @44
    @59
    ccvm
    @26
    cC
    wceq
    #
    @28
    cJ
    wceq
    #
    wa
    #
    @42
    @58
    vf
    @43
    @3
    @26
    cC
    @28
    cJ
    ccn
    oveq12
    @63
    @40
    @57
    vx
    @41
    cX
    @63
    @41
    cJ
    cuni
    cX
    @63
    @28
    cJ
    @61
    @62
    simpr
    #
    unieqd
    iscvm.2
    syl6eqr
    @63
    @39
    @56
    vk
    @28
    cJ
    @64
    @63
    @38
    @55
    @7
    @63
    @34
    @52
    vs
    @37
    @54
    @63
    @35
    @53
    @36
    @63
    @26
    cC
    @61
    @62
    simpl
    pweqd
    difeq1d
    @63
    @33
    @51
    @22
    @63
    @32
    @50
    vu
    @17
    @63
    @31
    @49
    @24
    @63
    @30
    @48
    @25
    @61
    @62
    @27
    @46
    @29
    @47
    chmeo
    @26
    cC
    @23
    crest
    oveq1
    @28
    cJ
    @6
    crest
    oveq1
    oveqan12d
    eleq2d
    anbi2d
    ralbidv
    anbi2d
    rexeqbidv
    anbi2d
    rexeqbidv
    raleqbidv
    rabeqbidv
    @45
    @58
    vf
    @3
    cC
    cJ
    ccn
    ovex
    rabex
    ovmpt2a
    eleq2d
    @2
    @13
    @4
    @7
    @18
    cF
    ccnv
    #
    @6
    cima
    #
    wceq
    #
    @24
    cF
    @23
    cres
    #
    @48
    wcel
    #
    wa
    #
    vu
    @17
    wral
    #
    wa
    #
    vs
    @54
    wrex
    #
    wa
    #
    vk
    cJ
    wrex
    #
    vx
    cX
    wral
    #
    wa
    @60
    @2
    @12
    @76
    @4
    @2
    @11
    @75
    vx
    cX
    @2
    @10
    @74
    vk
    cJ
    @2
    @6
    cJ
    wcel
    #
    wa
    #
    @9
    @73
    @7
    @78
    @9
    @72
    vs
    @54
    crab
    #
    c0
    wne
    @73
    @78
    @8
    @79
    c0
    @77
    @77
    @79
    cvv
    wcel
    #
    @8
    @79
    wceq
    @2
    @77
    id
    @2
    @53
    cvv
    wcel
    #
    @54
    cvv
    wcel
    @80
    @0
    @81
    @1
    cC
    ctop
    pwexg
    adantr
    @53
    @36
    cvv
    difexg
    @72
    vs
    @54
    cvv
    rabexg
    3syl
    vk
    cJ
    @79
    cvv
    cS
    iscvm.1
    fvmpt2
    syl2anr
    neeq1d
    @72
    vs
    @54
    rabn0
    syl6bb
    anbi2d
    rexbidva
    ralbidv
    anbi2d
    @58
    @76
    vf
    cF
    @3
    @19
    cF
    wceq
    #
    @57
    @75
    vx
    cX
    @82
    @56
    @74
    vk
    cJ
    @82
    @55
    @73
    @7
    @82
    @52
    @72
    vs
    @54
    @82
    @22
    @67
    @51
    @71
    @82
    @21
    @66
    @18
    @82
    @20
    @65
    @6
    @19
    cF
    cnveq
    imaeq1d
    eqeq2d
    @82
    @50
    @70
    vu
    @17
    @82
    @49
    @69
    @24
    @82
    @25
    @68
    @48
    @19
    cF
    @23
    reseq1
    eleq1d
    anbi2d
    ralbidv
    anbi12d
    rexbidv
    anbi2d
    rexbidv
    ralbidv
    elrab
    syl6bbr
    bitr4d
    biadan2
    3bitr4ri
end
