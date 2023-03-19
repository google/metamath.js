include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cuni.mm"
include "cv.mm"
include "cphtpc.mm"
include "cec.mm"
include "cmpt.mm"
include "crn.mm"
include "wfun.mm"
include "ccom.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "fvex.mm"
include "ecexg.mm"
include "mp1i.mm"
include "eqid.mm"
include "ctopon.mm"
include "ctop.mm"
include "ccn.mm"
include "co.mm"
include "cntop2.mm"
include "syl.mm"
include "toptopon.mm"
include "sylib.mm"
include "adantr.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "cii.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "w3a.mm"
include "a1i.mm"
include "pi1eluni.mm"
include "biimpa.mm"
include "simp1d.mm"
include "cnco.mm"
include "syl2anc.mm"
include "cicc.mm"
include "iitopon.mm"
include "0elunit.mm"
include "fvco3.mm"
include "sylancl.mm"
include "simp2d.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "1elunit.mm"
include "simp3d.mm"
include "elpi1i.mm"
include "eceq1.mm"
include "coeq2.mm"
include "eceq1d.mm"
include "wer.mm"
include "phtpcer.mm"
include "wbr.mm"
include "simpr3.mm"
include "simpr1.mm"
include "wb.mm"
include "mpbid.mm"
include "erth.mm"
include "mpbird.mm"
include "phtpcco2.mm"
include "erthi.mm"
include "fliftfund.mm"
include "fliftf.mm"
include "cqs.mm"
include "pi1bas2.mm"
include "wrex.mm"
include "cab.mm"
include "df-qs.mm"
include "rnmpt.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "feq2d.mm"

theorem pi1cof
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vh: setvar h
  let vf: setvar f
  let vz: setvar z
  let vy: setvar y
  let cT: class T
  assume pi1co.p: |- P = ( J pi1 A )
  assume pi1co.q: |- Q = ( K pi1 B )
  assume pi1co.v: |- V = ( Base ` P )
  assume pi1co.g: |- G = ran ( g e. U. V |-> <. [ g ] ( ~=ph ` J ) , [ ( F o. g ) ] ( ~=ph ` K ) >. )
  assume pi1co.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1co.f: |- ( ph -> F e. ( J Cn K ) )
  assume pi1co.a: |- ( ph -> A e. X )
  assume pi1co.b: |- ( ph -> ( F ` A ) = B )

  disjoint A g
  disjoint F g
  disjoint J g
  disjoint g ph
  disjoint K g
  disjoint P g
  disjoint Q g
  disjoint V g
  disjoint g s
  disjoint A s
  disjoint g h
  disjoint h s
  disjoint F h
  disjoint F s
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f z
  disjoint J f
  disjoint g z
  disjoint h z
  disjoint J h
  disjoint s z
  disjoint J s
  disjoint J z
  disjoint f y
  disjoint f ph
  disjoint g y
  disjoint h y
  disjoint h ph
  disjoint s y
  disjoint ph s
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint G f
  disjoint G h
  disjoint G y
  disjoint G z
  disjoint K h
  disjoint K s
  disjoint P f
  disjoint P h
  disjoint P s
  disjoint P y
  disjoint P z
  disjoint T g
  disjoint T s
  disjoint Q f
  disjoint Q h
  disjoint Q s
  disjoint Q y
  disjoint Q z
  disjoint V f
  disjoint V h
  disjoint V s
  disjoint V y
  disjoint V z
  assert |- ( ph -> G : V --> ( Base ` Q ) )

  proof
    wph
    cV
    cQ
    cbs
    cfv
    #
    cG
    wf
    vg
    cV
    cuni
    #
    vg
    cv
    #
    cJ
    cphtpc
    cfv
    #
    cec
    #
    cmpt
    #
    crn
    #
    @0
    cG
    wf
    #
    wph
    cG
    wfun
    @7
    wph
    vg
    vh
    @4
    cF
    @2
    ccom
    #
    cK
    cphtpc
    cfv
    #
    cec
    #
    vh
    cv
    #
    @3
    cec
    #
    cF
    @11
    ccom
    #
    @9
    cec
    cvv
    @0
    cG
    @1
    pi1co.g
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    wph
    @2
    @1
    wcel
    #
    wa
    #
    cJ
    cphtpc
    fvex
    @2
    cvv
    @3
    ecexg
    mp1i
    #
    @15
    @0
    @8
    cQ
    cK
    cK
    cuni
    #
    cB
    pi1co.q
    @0
    eqid
    wph
    cK
    @17
    ctopon
    cfv
    wcel
    #
    @14
    wph
    cK
    ctop
    wcel
    #
    @18
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @19
    pi1co.f
    cF
    cJ
    cK
    cntop2
    syl
    cK
    @17
    @17
    eqid
    toptopon
    sylib
    #
    adantr
    wph
    cB
    @17
    wcel
    @14
    wph
    cA
    cF
    cfv
    #
    cB
    @17
    pi1co.b
    wph
    cX
    @17
    cA
    cF
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @18
    @20
    cX
    @17
    cF
    wf
    pi1co.j
    @21
    pi1co.f
    cF
    cJ
    cK
    cX
    @17
    cnf2
    syl3anc
    pi1co.a
    ffvelrnd
    eqeltrrd
    adantr
    @15
    @2
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    @20
    @8
    cii
    cK
    ccn
    co
    #
    wcel
    @15
    @25
    cc0
    @2
    cfv
    #
    cA
    wceq
    #
    c1
    @2
    cfv
    #
    cA
    wceq
    #
    wph
    @14
    @25
    @28
    @30
    w3a
    #
    wph
    cV
    @2
    cP
    cJ
    cX
    cA
    pi1co.p
    pi1co.j
    pi1co.a
    cV
    cP
    cbs
    cfv
    wceq
    wph
    pi1co.v
    a1i
    #
    pi1eluni
    #
    biimpa
    #
    simp1d
    #
    wph
    @20
    @14
    pi1co.f
    adantr
    @2
    cF
    cii
    cJ
    cK
    cnco
    syl2anc
    @15
    cc0
    @8
    cfv
    #
    @27
    cF
    cfv
    #
    @22
    cB
    @15
    cc0
    c1
    cicc
    co
    #
    cX
    @2
    wf
    #
    cc0
    @38
    wcel
    @36
    @37
    wceq
    @15
    cii
    @38
    ctopon
    cfv
    wcel
    #
    @23
    @25
    @39
    @40
    @15
    iitopon
    a1i
    wph
    @23
    @14
    pi1co.j
    adantr
    @35
    @2
    cii
    cJ
    @38
    cX
    cnf2
    syl3anc
    #
    0elunit
    @38
    cX
    cc0
    cF
    @2
    fvco3
    sylancl
    @15
    @27
    cA
    cF
    @15
    @25
    @28
    @30
    @34
    simp2d
    fveq2d
    wph
    @22
    cB
    wceq
    @14
    pi1co.b
    adantr
    #
    3eqtrd
    @15
    c1
    @8
    cfv
    #
    @29
    cF
    cfv
    #
    @22
    cB
    @15
    @39
    c1
    @38
    wcel
    @43
    @44
    wceq
    @41
    1elunit
    @38
    cX
    c1
    cF
    @2
    fvco3
    sylancl
    @15
    @29
    cA
    cF
    @15
    @25
    @28
    @30
    @34
    simp3d
    fveq2d
    @42
    3eqtrd
    elpi1i
    #
    @2
    @11
    @3
    eceq1
    @2
    @11
    wceq
    @8
    @13
    @9
    @2
    @11
    cF
    coeq2
    eceq1d
    wph
    @14
    @11
    @1
    wcel
    #
    @4
    @12
    wceq
    #
    w3a
    #
    wa
    #
    @8
    @13
    @9
    @26
    @26
    @9
    wer
    @49
    cK
    phtpcer
    a1i
    @49
    cF
    @2
    @11
    cJ
    cK
    @49
    @2
    @11
    @3
    wbr
    @47
    wph
    @14
    @46
    @47
    simpr3
    @49
    @2
    @11
    @3
    @24
    @24
    @3
    wer
    @49
    cJ
    phtpcer
    a1i
    @49
    @25
    @28
    @30
    @49
    @14
    @31
    wph
    @14
    @46
    @47
    simpr1
    wph
    @14
    @31
    wb
    @48
    @33
    adantr
    mpbid
    simp1d
    erth
    mpbird
    wph
    @20
    @48
    pi1co.f
    adantr
    phtpcco2
    erthi
    fliftfund
    wph
    vg
    @4
    @10
    cvv
    @0
    cG
    @1
    pi1co.g
    @16
    @45
    fliftf
    mpbid
    wph
    cV
    @6
    @0
    cG
    wph
    cV
    @1
    @3
    cqs
    #
    @6
    wph
    cV
    cP
    cJ
    cX
    cA
    pi1co.p
    pi1co.j
    pi1co.a
    @32
    pi1bas2
    @50
    vs
    cv
    @4
    wceq
    vg
    @1
    wrex
    vs
    cab
    @6
    vg
    vs
    @1
    @3
    df-qs
    vg
    vs
    @1
    @4
    @5
    @5
    eqid
    rnmpt
    eqtr4i
    syl6eq
    feq2d
    mpbird
end
