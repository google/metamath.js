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
include "cpco.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "ctopon.mm"
include "adantr.mm"
include "c1.mm"
include "cicc.mm"
include "cii.mm"
include "ccn.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "0elunit.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "wceq.mm"
include "w3a.mm"
include "pi1eluni.mm"
include "biimpa.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "elpi1i.mm"
include "eqid.mm"
include "1elunit.mm"
include "pcocn.mm"
include "pco0.mm"
include "3eqtr4rd.mm"
include "eqtr4d.mm"
include "pco1.mm"
include "eqtrd.mm"
include "eceq1.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eceq1d.mm"
include "wer.mm"
include "phtpcer.mm"
include "3ad2antr1.mm"
include "erref.mm"
include "wbr.mm"
include "simpr3.mm"
include "erth.mm"
include "mpbird.mm"
include "pcohtpy.mm"
include "erthi.mm"
include "fliftfund.mm"
include "fliftf.mm"
include "mpbid.mm"
include "cqs.mm"
include "pi1bas2.mm"
include "wrex.mm"
include "cab.mm"
include "df-qs.mm"
include "rnmpt.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "feq2d.mm"

theorem pi1xfrf
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vs: setvar s
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cH: class H
  assume pi1xfr.p: |- P = ( J pi1 ( F ` 0 ) )
  assume pi1xfr.q: |- Q = ( J pi1 ( F ` 1 ) )
  assume pi1xfr.b: |- B = ( Base ` P )
  assume pi1xfr.g: |- G = ran ( g e. U. B |-> <. [ g ] ( ~=ph ` J ) , [ ( I ( *p ` J ) ( g ( *p ` J ) F ) ) ] ( ~=ph ` J ) >. )
  assume pi1xfr.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1xfr.f: |- ( ph -> F e. ( II Cn J ) )
  assume pi1xfrval.i: |- ( ph -> I e. ( II Cn J ) )
  assume pi1xfrval.1: |- ( ph -> ( F ` 1 ) = ( I ` 0 ) )
  assume pi1xfrval.2: |- ( ph -> ( I ` 1 ) = ( F ` 0 ) )

  disjoint B g
  disjoint F g
  disjoint I g
  disjoint g ph
  disjoint J g
  disjoint P g
  disjoint Q g
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g s
  disjoint g u
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint h s
  disjoint h u
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F h
  disjoint F s
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint I h
  disjoint I s
  disjoint I u
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint A g
  disjoint A s
  disjoint A x
  disjoint G f
  disjoint G h
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H s
  disjoint H z
  disjoint f ph
  disjoint h ph
  disjoint ph s
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint J f
  disjoint J h
  disjoint J s
  disjoint J u
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint P f
  disjoint P h
  disjoint P s
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q f
  disjoint Q h
  disjoint Q s
  disjoint Q x
  disjoint Q y
  disjoint Q z
  assert |- ( ph -> G : B --> ( Base ` Q ) )

  proof
    wph
    cB
    cQ
    cbs
    cfv
    #
    cG
    wf
    vg
    cB
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
    cI
    @2
    cF
    cJ
    cpco
    cfv
    #
    co
    #
    @8
    co
    #
    @3
    cec
    #
    vh
    cv
    #
    @3
    cec
    #
    cI
    @12
    cF
    @8
    co
    #
    @8
    co
    #
    @3
    cec
    cB
    @0
    cG
    @1
    pi1xfr.g
    wph
    @2
    @1
    wcel
    #
    wa
    #
    cB
    @2
    cP
    cJ
    cX
    cc0
    cF
    cfv
    #
    pi1xfr.p
    pi1xfr.b
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @16
    pi1xfr.j
    adantr
    #
    wph
    @18
    cX
    wcel
    #
    @16
    wph
    cc0
    c1
    cicc
    co
    #
    cX
    cF
    wf
    #
    cc0
    @22
    wcel
    @21
    wph
    cii
    @22
    ctopon
    cfv
    wcel
    #
    @19
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    @23
    @24
    wph
    iitopon
    a1i
    pi1xfr.j
    pi1xfr.f
    cF
    cii
    cJ
    @22
    cX
    cnf2
    syl3anc
    #
    0elunit
    @22
    cX
    cc0
    cF
    ffvelrn
    sylancl
    #
    adantr
    @17
    @2
    @25
    wcel
    #
    cc0
    @2
    cfv
    #
    @18
    wceq
    #
    c1
    @2
    cfv
    @18
    wceq
    #
    wph
    @16
    @29
    @31
    @32
    w3a
    wph
    cB
    @2
    cP
    cJ
    cX
    @18
    pi1xfr.p
    pi1xfr.j
    @28
    cB
    cP
    cbs
    cfv
    wceq
    wph
    pi1xfr.b
    a1i
    #
    pi1eluni
    biimpa
    #
    simp1d
    #
    @17
    @29
    @31
    @32
    @34
    simp2d
    #
    @17
    @29
    @31
    @32
    @34
    simp3d
    #
    elpi1i
    #
    @17
    @0
    @10
    cQ
    cJ
    cX
    c1
    cF
    cfv
    #
    pi1xfr.q
    @0
    eqid
    @20
    wph
    @39
    cX
    wcel
    #
    @16
    wph
    @23
    c1
    @22
    wcel
    @40
    @27
    1elunit
    @22
    cX
    c1
    cF
    ffvelrn
    sylancl
    adantr
    @17
    cI
    @9
    cJ
    wph
    cI
    @25
    wcel
    #
    @16
    pi1xfrval.i
    adantr
    #
    @17
    @2
    cF
    cJ
    @35
    wph
    @26
    @16
    pi1xfr.f
    adantr
    #
    @37
    pcocn
    #
    @17
    @30
    @18
    cc0
    @9
    cfv
    #
    c1
    cI
    cfv
    #
    @36
    @17
    @2
    cF
    cJ
    @35
    @43
    pco0
    wph
    @46
    @18
    wceq
    #
    @16
    pi1xfrval.2
    adantr
    3eqtr4rd
    pcocn
    @17
    cc0
    @10
    cfv
    cc0
    cI
    cfv
    #
    @39
    @17
    cI
    @9
    cJ
    @42
    @44
    pco0
    wph
    @39
    @48
    wceq
    @16
    pi1xfrval.1
    adantr
    eqtr4d
    @17
    c1
    @10
    cfv
    c1
    @9
    cfv
    @39
    @17
    cI
    @9
    cJ
    @42
    @44
    pco1
    @17
    @2
    cF
    cJ
    @35
    @43
    pco1
    eqtrd
    elpi1i
    #
    @2
    @12
    @3
    eceq1
    @2
    @12
    wceq
    #
    @10
    @15
    @3
    @50
    @9
    @14
    cI
    @8
    @2
    @12
    cF
    @8
    oveq1
    oveq2d
    eceq1d
    wph
    @16
    @12
    @1
    wcel
    #
    @4
    @13
    wceq
    #
    w3a
    #
    wa
    #
    @10
    @15
    @3
    @25
    @25
    @3
    wer
    @54
    cJ
    phtpcer
    a1i
    #
    @54
    cI
    @9
    cI
    cJ
    @14
    @54
    @30
    @18
    @45
    @46
    wph
    @51
    @16
    @31
    @52
    @36
    3ad2antr1
    @54
    @2
    cF
    cJ
    wph
    @51
    @16
    @29
    @52
    @35
    3ad2antr1
    #
    wph
    @26
    @53
    pi1xfr.f
    adantr
    #
    pco0
    wph
    @47
    @53
    pi1xfrval.2
    adantr
    3eqtr4rd
    @54
    cI
    @3
    @25
    @55
    wph
    @41
    @53
    pi1xfrval.i
    adantr
    erref
    @54
    @2
    cF
    @12
    cJ
    cF
    wph
    @51
    @16
    @32
    @52
    @37
    3ad2antr1
    @54
    @2
    @12
    @3
    wbr
    @52
    wph
    @16
    @51
    @52
    simpr3
    @54
    @2
    @12
    @3
    @25
    @55
    @56
    erth
    mpbird
    @54
    cF
    @3
    @25
    @55
    @57
    erref
    pcohtpy
    pcohtpy
    erthi
    fliftfund
    wph
    vg
    @4
    @11
    cB
    @0
    cG
    @1
    pi1xfr.g
    @38
    @49
    fliftf
    mpbid
    wph
    cB
    @6
    @0
    cG
    wph
    cB
    @1
    @3
    cqs
    #
    @6
    wph
    cB
    cP
    cJ
    cX
    @18
    pi1xfr.p
    pi1xfr.j
    @28
    @33
    pi1bas2
    @58
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
