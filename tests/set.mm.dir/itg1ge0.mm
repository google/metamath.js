include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "c0p.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "crn.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "cfn.mm"
include "wss.mm"
include "i1frn.mm"
include "difss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "adantr.mm"
include "cr.mm"
include "wf.mm"
include "i1ff.mm"
include "frn.mm"
include "syl.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "i1fima2sn.mm"
include "adantlr.mm"
include "remulcld.mm"
include "eldifi.mm"
include "wral.mm"
include "cc.mm"
include "cvv.mm"
include "wfn.mm"
include "cxp.mm"
include "0cn.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "df-0p.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "a1i.mm"
include "ffn.mm"
include "cnex.mm"
include "reex.mm"
include "cin.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "0pval.mm"
include "adantl.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "biimpa.mm"
include "wb.mm"
include "breq2.mm"
include "ralrn.mm"
include "mpbird.mm"
include "r19.21bi.mm"
include "sylan2.mm"
include "i1fima.mm"
include "ad2antrr.mm"
include "covol.mm"
include "mblss.mm"
include "ovolge0.mm"
include "mblvol.mm"
include "breqtrrd.mm"
include "mulge0d.mm"
include "fsumge0.mm"
include "itg1val.mm"

theorem itg1ge0
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( ( F e. dom S.1 /\ 0p oR <_ F ) -> 0 <_ ( S.1 ` F ) )

  proof
    cF
    citg1
    cdm
    wcel
    #
    c0p
    cF
    cle
    cofr
    wbr
    #
    wa
    #
    cc0
    cF
    crn
    #
    cc0
    csn
    #
    cdif
    #
    vx
    cv
    #
    cF
    ccnv
    @6
    csn
    #
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vx
    csu
    #
    cF
    citg1
    cfv
    #
    cle
    @2
    @5
    @10
    vx
    @0
    @5
    cfn
    wcel
    #
    @1
    @0
    @3
    cfn
    wcel
    @5
    @3
    wss
    @13
    cF
    i1frn
    @3
    @4
    difss
    @3
    @5
    ssfi
    sylancl
    adantr
    @2
    @6
    @5
    wcel
    #
    wa
    #
    @6
    @9
    @2
    @5
    cr
    @6
    @2
    @3
    cr
    @4
    @2
    cr
    cr
    cF
    wf
    #
    @3
    cr
    wss
    @0
    @16
    @1
    cF
    i1ff
    #
    adantr
    cr
    cr
    cF
    frn
    syl
    ssdifssd
    sselda
    #
    @0
    @14
    @9
    cr
    wcel
    @1
    @6
    @3
    cF
    i1fima2sn
    adantlr
    #
    remulcld
    @15
    @6
    @9
    @18
    @19
    @14
    @2
    @6
    @3
    wcel
    cc0
    @6
    cle
    wbr
    #
    @6
    @3
    @4
    eldifi
    @2
    @20
    vx
    @3
    @2
    @20
    vx
    @3
    wral
    #
    cc0
    vy
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vy
    cr
    wral
    #
    @0
    @1
    @25
    @0
    vy
    cc
    cr
    cc0
    @23
    cle
    cr
    c0p
    cF
    cvv
    cvv
    c0p
    cc
    wfn
    #
    @0
    @26
    cc
    @4
    cxp
    #
    cc
    wfn
    #
    cc0
    cc
    wcel
    @28
    0cn
    cc
    cc0
    cc
    fnconstg
    ax-mp
    cc
    c0p
    @27
    df-0p
    fneq1i
    mpbir
    a1i
    @0
    @16
    cF
    cr
    wfn
    #
    @17
    cr
    cr
    cF
    ffn
    syl
    #
    cc
    cvv
    wcel
    @0
    cnex
    a1i
    cr
    cvv
    wcel
    @0
    reex
    a1i
    cr
    cc
    wss
    cc
    cr
    cin
    cr
    wceq
    ax-resscn
    cr
    cc
    sseqin2
    mpbi
    @22
    cc
    wcel
    @22
    c0p
    cfv
    cc0
    wceq
    @0
    @22
    0pval
    adantl
    @0
    @22
    cr
    wcel
    wa
    @23
    eqidd
    ofrfval
    biimpa
    @2
    @29
    @21
    @25
    wb
    @0
    @29
    @1
    @30
    adantr
    @20
    @24
    vx
    vy
    cr
    cF
    @6
    @23
    cc0
    cle
    breq2
    ralrn
    syl
    mpbird
    r19.21bi
    sylan2
    @15
    @8
    cvol
    cdm
    wcel
    #
    cc0
    @9
    cle
    wbr
    @0
    @31
    @1
    @14
    @7
    cF
    i1fima
    ad2antrr
    @31
    cc0
    @8
    covol
    cfv
    #
    @9
    cle
    @31
    @8
    cr
    wss
    cc0
    @32
    cle
    wbr
    @8
    mblss
    @8
    ovolge0
    syl
    @8
    mblvol
    breqtrrd
    syl
    mulge0d
    fsumge0
    @0
    @12
    @11
    wceq
    @1
    vx
    cF
    itg1val
    adantr
    breqtrrd
end
