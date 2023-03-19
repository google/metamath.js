include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "csn.mm"
include "cdif.mm"
include "cpw.mm"
include "c0.mm"
include "crab.mm"
include "df-ima.mm"
include "wss.mm"
include "wral.mm"
include "cdm.mm"
include "wnel.mm"
include "wceq.mm"
include "wb.mm"
include "fveq2.mm"
include "neleq2.mm"
include "syl.mm"
include "elrab2.mm"
include "wf.mm"
include "wi.mm"
include "upgrf.mm"
include "ffvelrn.mm"
include "breq1d.mm"
include "elrab.mm"
include "wne.mm"
include "eldifsn.mm"
include "simpl.mm"
include "elpwi.mm"
include "adantr.mm"
include "simpr.mm"
include "elpwdifsn.mm"
include "syl3anc.mm"
include "ex.mm"
include "sylbi.mm"
include "imp.mm"
include "eldifsni.mm"
include "sylanbrc.mm"
include "elrabd.mm"
include "a1d.mm"
include "com23.mm"
include "imp4b.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "wfun.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "uhgrfun.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "funimass4.mm"
include "sylancl.mm"
include "mpbird.mm"
include "syl5eqssr.mm"

theorem upgrreslem
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
  assert |- ( ( G e. UPGraph /\ N e. V ) -> ran ( E |` F ) C_ { p e. ( ~P ( V \ { N } ) \ { (/) } ) | ( # ` p ) <_ 2 } )

  proof
    cG
    cupgr
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
    cle
    wbr
    #
    vp
    cV
    cN
    csn
    cdif
    cpw
    #
    c0
    csn
    #
    cdif
    #
    crab
    #
    cE
    cF
    df-ima
    @2
    @3
    @10
    wss
    #
    vj
    cv
    #
    cE
    cfv
    #
    @10
    wcel
    #
    vj
    cF
    wral
    #
    @2
    @14
    vj
    cF
    @12
    cF
    wcel
    @12
    cE
    cdm
    #
    wcel
    #
    cN
    @13
    wnel
    #
    wa
    @2
    @14
    cN
    vi
    cv
    #
    cE
    cfv
    #
    wnel
    #
    @18
    vi
    @12
    @16
    cF
    @19
    @12
    wceq
    @20
    @13
    wceq
    @21
    @18
    wb
    @19
    @12
    cE
    fveq2
    @20
    @13
    cN
    neleq2
    syl
    upgrres.f
    elrab2
    @0
    @1
    @17
    @18
    @14
    @0
    @16
    @6
    vp
    cV
    cpw
    #
    @8
    cdif
    #
    crab
    #
    cE
    wf
    #
    @1
    @17
    @18
    @14
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
    upgrf
    @25
    @17
    @1
    @26
    @25
    @17
    @1
    @26
    wi
    #
    @25
    @17
    wa
    @13
    @24
    wcel
    #
    @27
    @16
    @24
    @12
    cE
    ffvelrn
    @28
    @13
    @23
    wcel
    #
    @13
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    wa
    #
    @27
    @6
    @31
    vp
    @13
    @23
    @4
    @13
    wceq
    @5
    @30
    c2
    cle
    @4
    @13
    chash
    fveq2
    breq1d
    #
    elrab
    @32
    @26
    @1
    @32
    @18
    @14
    @32
    @18
    wa
    #
    @6
    @31
    vp
    @13
    @9
    @33
    @34
    @13
    @7
    wcel
    #
    @13
    c0
    wne
    #
    @13
    @9
    wcel
    @32
    @18
    @35
    @29
    @18
    @35
    wi
    #
    @31
    @29
    @13
    @22
    wcel
    #
    @36
    wa
    @37
    @13
    @22
    c0
    eldifsn
    @38
    @37
    @36
    @38
    @18
    @35
    @38
    @18
    wa
    @38
    @13
    cV
    wss
    #
    @18
    @35
    @38
    @18
    simpl
    @38
    @39
    @18
    @13
    cV
    elpwi
    adantr
    @38
    @18
    simpr
    cN
    @13
    cV
    @22
    elpwdifsn
    syl3anc
    ex
    adantr
    sylbi
    adantr
    imp
    @32
    @36
    @18
    @29
    @36
    @31
    @13
    @22
    c0
    eldifsni
    adantr
    adantr
    @13
    @7
    c0
    eldifsn
    sylanbrc
    @32
    @31
    @18
    @29
    @31
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
    @16
    wss
    @11
    @15
    wb
    @0
    @40
    @1
    @0
    cG
    cuhgr
    wcel
    @40
    cG
    upgruhgr
    cE
    cG
    upgrres.e
    uhgrfun
    syl
    adantr
    cF
    @21
    vi
    @16
    crab
    @16
    upgrres.f
    @21
    vi
    @16
    ssrab2
    eqsstri
    vj
    cF
    @10
    cE
    funimass4
    sylancl
    mpbird
    syl5eqssr
end
