include "cuhgr.mm"
include "wcel.mm"
include "wa.mm"
include "csubgr.mm"
include "wbr.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "cima.mm"
include "cpw.mm"
include "difssd.mm"
include "uhgrspan1lem3.mm"
include "resresdm.mm"
include "mp1i.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wfun.mm"
include "uhgrfun.mm"
include "fvelima.mm"
include "ex.mm"
include "syl.mm"
include "adantr.mm"
include "wnel.mm"
include "weq.mm"
include "eqidd.mm"
include "fveq2.mm"
include "neleq12d.mm"
include "elrab2.mm"
include "cvv.mm"
include "fvexd.mm"
include "uhgrss.mm"
include "ad2ant2r.mm"
include "simprr.mm"
include "elpwdifsn.mm"
include "syl3anc.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "syl5ibrcom.mm"
include "syl5bi.mm"
include "rexlimdv.mm"
include "syld.mm"
include "ssrdv.mm"
include "w3a.mm"
include "cop.mm"
include "opex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cvtx.mm"
include "uhgrspan1lem2.mm"
include "eqcomi.mm"
include "eqid.mm"
include "crn.mm"
include "cedg.mm"
include "rneqi.mm"
include "edgval.mm"
include "df-ima.mm"
include "3eqtr4ri.mm"
include "issubgr.mm"
include "sylan2.mm"
include "mpbir3and.mm"

theorem uhgrspan1
  let cS: class S
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let vc: setvar c
  let vj: setvar j
  assume uhgrspan1.v: |- V = ( Vtx ` G )
  assume uhgrspan1.i: |- I = ( iEdg ` G )
  assume uhgrspan1.f: |- F = { i e. dom I | N e/ ( I ` i ) }
  assume uhgrspan1.s: |- S = <. ( V \ { N } ) , ( I |` F ) >.

  disjoint I i
  disjoint N i
  disjoint F c
  disjoint F j
  disjoint c j
  disjoint G c
  disjoint G j
  disjoint I c
  disjoint I j
  disjoint c i
  disjoint i j
  disjoint N c
  disjoint N j
  disjoint V c
  disjoint V j
  assert |- ( ( G e. UHGraph /\ N e. V ) -> S SubGraph G )

  proof
    cG
    cuhgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cS
    cG
    csubgr
    wbr
    #
    cV
    cN
    csn
    #
    cdif
    #
    cV
    wss
    #
    cS
    ciedg
    cfv
    #
    cI
    @7
    cdm
    cres
    wceq
    #
    cI
    cF
    cima
    #
    @5
    cpw
    #
    wss
    #
    @2
    cV
    @4
    difssd
    @7
    cI
    cF
    cres
    #
    wceq
    @8
    @2
    cS
    vi
    cF
    cG
    cI
    cN
    cV
    uhgrspan1.v
    uhgrspan1.i
    uhgrspan1.f
    uhgrspan1.s
    uhgrspan1lem3
    #
    cF
    cI
    @7
    resresdm
    mp1i
    @2
    vc
    @9
    @10
    @2
    vc
    cv
    #
    @9
    wcel
    #
    vj
    cv
    #
    cI
    cfv
    #
    @14
    wceq
    #
    vj
    cF
    wrex
    #
    @14
    @10
    wcel
    #
    @0
    @15
    @19
    wi
    #
    @1
    @0
    cI
    wfun
    #
    @21
    cI
    cG
    uhgrspan1.i
    uhgrfun
    @22
    @15
    @19
    vj
    @14
    cF
    cI
    fvelima
    ex
    syl
    adantr
    @2
    @18
    @20
    vj
    cF
    @16
    cF
    wcel
    @16
    cI
    cdm
    #
    wcel
    #
    cN
    @17
    wnel
    #
    wa
    #
    @2
    @18
    @20
    wi
    #
    cN
    vi
    cv
    #
    cI
    cfv
    #
    wnel
    @25
    vi
    @16
    @23
    cF
    vi
    vj
    weq
    #
    cN
    cN
    @29
    @17
    @30
    cN
    eqidd
    @28
    @16
    cI
    fveq2
    neleq12d
    uhgrspan1.f
    elrab2
    @2
    @26
    @27
    @2
    @26
    wa
    #
    @20
    @18
    @17
    @10
    wcel
    #
    @31
    @17
    cvv
    wcel
    @17
    cV
    wss
    #
    @25
    @32
    @31
    @16
    cI
    fvexd
    @0
    @24
    @33
    @1
    @25
    cI
    @16
    cG
    cV
    uhgrspan1.v
    uhgrspan1.i
    uhgrss
    ad2ant2r
    @2
    @24
    @25
    simprr
    cN
    @17
    cV
    cvv
    elpwdifsn
    syl3anc
    @20
    @32
    wb
    @14
    @17
    @14
    @17
    @10
    eleq1
    eqcoms
    syl5ibrcom
    ex
    syl5bi
    rexlimdv
    syld
    ssrdv
    @1
    @0
    cS
    cvv
    wcel
    #
    @3
    @6
    @8
    @11
    w3a
    wb
    @34
    @1
    cS
    @5
    @12
    cop
    cvv
    uhgrspan1.s
    @5
    @12
    opex
    eqeltri
    a1i
    cV
    cI
    cS
    cvv
    @9
    cG
    @7
    @5
    cuhgr
    cS
    cvtx
    cfv
    @5
    cS
    vi
    cF
    cG
    cI
    cN
    cV
    uhgrspan1.v
    uhgrspan1.i
    uhgrspan1.f
    uhgrspan1.s
    uhgrspan1lem2
    eqcomi
    uhgrspan1.v
    @7
    eqid
    uhgrspan1.i
    @7
    crn
    @12
    crn
    cS
    cedg
    cfv
    @9
    @7
    @12
    @13
    rneqi
    cS
    edgval
    cI
    cF
    df-ima
    3eqtr4ri
    issubgr
    sylan2
    mpbir3and
end
