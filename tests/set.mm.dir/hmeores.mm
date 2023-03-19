include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cres.mm"
include "crest.mm"
include "cima.mm"
include "ccn.mm"
include "ccnv.mm"
include "hmeocn.mm"
include "adantr.mm"
include "cnrest.mm"
include "sylancom.mm"
include "cuni.mm"
include "ctopon.mm"
include "cfv.mm"
include "crn.mm"
include "wb.mm"
include "ctop.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "df-ima.mm"
include "eqimss2i.mm"
include "a1i.mm"
include "imassrn.mm"
include "wf.mm"
include "cnf.mm"
include "frn.mm"
include "syl5ss.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "wfun.mm"
include "wceq.mm"
include "hmeocnvcn.mm"
include "ffun.mm"
include "funcnvres.mm"
include "4syl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "cntop1.mm"
include "cdm.mm"
include "dfdm4.mm"
include "fssres.mm"
include "fdm.mm"
include "syl5eqr.mm"
include "eqimss.mm"
include "simpr.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem hmeores
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  assume hmeores.1: |- X = U. J


  assert |- ( ( F e. ( J Homeo K ) /\ Y C_ X ) -> ( F |` Y ) e. ( ( J |`t Y ) Homeo ( K |`t ( F " Y ) ) ) )

  proof
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    cY
    cX
    wss
    #
    wa
    #
    cF
    cY
    cres
    #
    cJ
    cY
    crest
    co
    #
    cK
    cF
    cY
    cima
    #
    crest
    co
    #
    ccn
    co
    wcel
    #
    @3
    ccnv
    #
    @6
    @4
    ccn
    co
    wcel
    #
    @3
    @4
    @6
    chmeo
    co
    wcel
    @2
    @3
    @4
    cK
    ccn
    co
    wcel
    #
    @7
    @0
    @1
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @10
    @0
    @11
    @1
    cF
    cJ
    cK
    hmeocn
    adantr
    #
    cY
    cF
    cJ
    cK
    cX
    hmeores.1
    cnrest
    sylancom
    @2
    cK
    cK
    cuni
    #
    ctopon
    cfv
    wcel
    #
    @3
    crn
    #
    @5
    wss
    #
    @5
    @13
    wss
    #
    @10
    @7
    wb
    @2
    cK
    ctop
    wcel
    #
    @14
    @2
    @11
    @18
    @12
    cF
    cJ
    cK
    cntop2
    syl
    cK
    @13
    @13
    eqid
    #
    toptopon
    sylib
    @16
    @2
    @5
    @15
    cF
    cY
    df-ima
    eqimss2i
    a1i
    @2
    @5
    cF
    crn
    #
    @13
    cF
    cY
    imassrn
    @2
    cX
    @13
    cF
    wf
    #
    @20
    @13
    wss
    @2
    @11
    @21
    @12
    cF
    cJ
    cK
    cX
    @13
    hmeores.1
    @19
    cnf
    syl
    #
    cX
    @13
    cF
    frn
    syl
    syl5ss
    #
    @5
    @3
    @4
    cK
    @13
    cnrest2
    syl3anc
    mpbid
    @2
    @8
    @6
    cJ
    ccn
    co
    #
    wcel
    #
    @9
    @2
    @8
    cF
    ccnv
    #
    @5
    cres
    #
    @24
    @2
    @26
    cK
    cJ
    ccn
    co
    wcel
    #
    @13
    cX
    @26
    wf
    @26
    wfun
    @8
    @27
    wceq
    @0
    @28
    @1
    cF
    cJ
    cK
    hmeocnvcn
    adantr
    #
    @26
    cK
    cJ
    @13
    cX
    @19
    hmeores.1
    cnf
    @13
    cX
    @26
    ffun
    cY
    cF
    funcnvres
    4syl
    @2
    @28
    @17
    @27
    @24
    wcel
    @29
    @23
    @5
    @26
    cK
    cJ
    @13
    @19
    cnrest
    syl2anc
    eqeltrd
    @2
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @8
    crn
    #
    cY
    wss
    #
    @1
    @25
    @9
    wb
    @2
    cJ
    ctop
    wcel
    #
    @30
    @2
    @11
    @33
    @12
    cF
    cJ
    cK
    cntop1
    syl
    cJ
    cX
    hmeores.1
    toptopon
    sylib
    @2
    @31
    cY
    wceq
    @32
    @2
    @31
    @3
    cdm
    #
    cY
    @3
    dfdm4
    @2
    cY
    @13
    @3
    wf
    #
    @34
    cY
    wceq
    @0
    @1
    @21
    @35
    @22
    cX
    @13
    cY
    cF
    fssres
    sylancom
    cY
    @13
    @3
    fdm
    syl
    syl5eqr
    @31
    cY
    eqimss
    syl
    @0
    @1
    simpr
    cY
    @8
    @6
    cJ
    cX
    cnrest2
    syl3anc
    mpbid
    @3
    @4
    @6
    ishmeo
    sylanbrc
end
