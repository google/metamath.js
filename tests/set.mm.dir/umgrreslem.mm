include "cumgr.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "cpw.mm"
include "crab.mm"
include "df-ima.mm"
include "wss.mm"
include "wral.mm"
include "cdm.mm"
include "wnel.mm"
include "weq.mm"
include "wb.mm"
include "fveq2.mm"
include "neleq2.mm"
include "syl.mm"
include "elrab2.mm"
include "wf.mm"
include "wi.mm"
include "umgrf.mm"
include "ffvelrn.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "simpll.mm"
include "elpwi.mm"
include "adantr.mm"
include "simpr.mm"
include "elpwdifsn.mm"
include "syl3anc.mm"
include "elrabd.mm"
include "ex.mm"
include "a1d.mm"
include "sylbi.mm"
include "com23.mm"
include "imp4b.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "wfun.mm"
include "cuhgr.mm"
include "umgruhgr.mm"
include "uhgrfun.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "funimass4.mm"
include "sylancl.mm"
include "mpbird.mm"
include "syl5eqssr.mm"

theorem umgrreslem
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vp: setvar p
  let vj: setvar j
  assume upgrres.v: |- V = ( Vtx ` G )
  assume upgrres.e: |- E = ( iEdg ` G )
  assume upgrres.f: |- F = { i e. dom E | N e/ ( E ` i ) }

  disjoint E i
  disjoint E p
  disjoint G p
  disjoint N i
  disjoint N p
  disjoint V p
  disjoint E j
  disjoint i j
  disjoint j p
  disjoint F j
  disjoint G j
  disjoint N j
  disjoint V j
  assert |- ( ( G e. UMGraph /\ N e. V ) -> ran ( E |` F ) C_ { p e. ~P ( V \ { N } ) | ( # ` p ) = 2 } )

  proof
    cG
    cumgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cE
    cF
    cres
    crn
    cE
    cF
    cima
    #
    vp
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vp
    cV
    cN
    csn
    cdif
    cpw
    #
    crab
    #
    cE
    cF
    df-ima
    @2
    @3
    @8
    wss
    #
    vj
    cv
    #
    cE
    cfv
    #
    @8
    wcel
    #
    vj
    cF
    wral
    #
    @2
    @12
    vj
    cF
    @10
    cF
    wcel
    @10
    cE
    cdm
    #
    wcel
    #
    cN
    @11
    wnel
    #
    wa
    @2
    @12
    cN
    vi
    cv
    #
    cE
    cfv
    #
    wnel
    #
    @16
    vi
    @10
    @14
    cF
    vi
    vj
    weq
    @18
    @11
    wceq
    @19
    @16
    wb
    @17
    @10
    cE
    fveq2
    @18
    @11
    cN
    neleq2
    syl
    upgrres.f
    elrab2
    @0
    @1
    @15
    @16
    @12
    @0
    @14
    @6
    vp
    cV
    cpw
    #
    crab
    #
    cE
    wf
    #
    @1
    @15
    @16
    @12
    wi
    #
    wi
    wi
    vp
    cE
    cG
    cV
    upgrres.v
    upgrres.e
    umgrf
    @22
    @15
    @1
    @23
    @22
    @15
    @1
    @23
    wi
    #
    @22
    @15
    wa
    @11
    @21
    wcel
    #
    @24
    @14
    @21
    @10
    cE
    ffvelrn
    @25
    @11
    @20
    wcel
    #
    @11
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    @24
    @6
    @28
    vp
    @11
    @20
    @4
    @11
    wceq
    @5
    @27
    c2
    @4
    @11
    chash
    fveq2
    eqeq1d
    #
    elrab
    @29
    @23
    @1
    @29
    @16
    @12
    @29
    @16
    wa
    #
    @6
    @28
    vp
    @11
    @7
    @30
    @31
    @26
    @11
    cV
    wss
    #
    @16
    @11
    @7
    wcel
    @26
    @28
    @16
    simpll
    @29
    @32
    @16
    @26
    @32
    @28
    @11
    cV
    elpwi
    adantr
    adantr
    @29
    @16
    simpr
    cN
    @11
    cV
    @20
    elpwdifsn
    syl3anc
    @29
    @28
    @16
    @26
    @28
    simpr
    adantr
    elrabd
    ex
    a1d
    sylbi
    syl
    ex
    com23
    syl
    imp4b
    syl5bi
    ralrimiv
    @2
    cE
    wfun
    #
    cF
    @14
    wss
    @9
    @13
    wb
    @0
    @33
    @1
    @0
    cG
    cuhgr
    wcel
    @33
    cG
    umgruhgr
    cE
    cG
    upgrres.e
    uhgrfun
    syl
    adantr
    cF
    @19
    vi
    @14
    crab
    @14
    upgrres.f
    @19
    vi
    @14
    ssrab2
    eqsstri
    vj
    cF
    @8
    cE
    funimass4
    sylancl
    mpbird
    syl5eqssr
end
