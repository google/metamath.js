include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "creps.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cfzo.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "wral.mm"
include "w3a.mm"
include "repsconst.mm"
include "eqeq2d.mm"
include "wb.mm"
include "fconst2g.mm"
include "adantr.mm"
include "wfn.mm"
include "wi.mm"
include "fconstfv.mm"
include "wss.mm"
include "simpr.mm"
include "snssi.mm"
include "jca.mm"
include "fss.mm"
include "iswrdi.mm"
include "3syl.mm"
include "ffzo0hash.mm"
include "expcom.mm"
include "ffn.mm"
include "syl11.mm"
include "adantl.mm"
include "imp.mm"
include "ex.mm"
include "syl5bir.mm"
include "expcomd.mm"
include "wrdf.mm"
include "oveq2.mm"
include "fneq2d.mm"
include "biimpd.mm"
include "a1d.mm"
include "com13.mm"
include "com12.mm"
include "impd.mm"
include "impbid.mm"
include "pm5.32rd.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "3bitr2d.mm"

theorem repsdf2
  let cS: class S
  let vi: setvar i
  let cN: class N
  let cV: class V
  let cW: class W

  disjoint N i
  disjoint S i
  disjoint W i
  assert |- ( ( S e. V /\ N e. NN0 ) -> ( W = ( S repeatS N ) <-> ( W e. Word V /\ ( # ` W ) = N /\ A. i e. ( 0 ..^ N ) ( W ` i ) = S ) ) )

  proof
    cS
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cW
    cS
    cN
    creps
    co
    #
    wceq
    cW
    cc0
    cN
    cfzo
    co
    #
    cS
    csn
    #
    cxp
    #
    wceq
    #
    @4
    @5
    cW
    wf
    #
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    wceq
    #
    vi
    cv
    cW
    cfv
    cS
    wceq
    vi
    @4
    wral
    #
    w3a
    #
    @2
    @3
    @6
    cW
    cS
    cN
    cV
    repsconst
    eqeq2d
    @0
    @8
    @7
    wb
    @1
    @4
    cS
    cV
    cW
    fconst2g
    adantr
    @2
    cW
    @4
    wfn
    #
    @12
    wa
    #
    @9
    @11
    wa
    #
    @12
    wa
    @8
    @13
    @2
    @12
    @14
    @16
    @2
    @12
    @14
    @16
    wb
    @2
    @12
    wa
    @14
    @16
    @2
    @12
    @14
    @16
    wi
    @2
    @14
    @12
    @16
    @15
    @8
    @2
    @16
    vi
    @4
    cS
    cW
    fconstfv
    #
    @2
    @8
    @16
    @2
    @8
    wa
    #
    @9
    @11
    @18
    @8
    @5
    cV
    wss
    #
    wa
    @4
    cV
    cW
    wf
    @9
    @18
    @8
    @19
    @2
    @8
    simpr
    @2
    @19
    @8
    @0
    @19
    @1
    cS
    cV
    snssi
    adantr
    adantr
    jca
    @4
    @5
    cV
    cW
    fss
    cV
    cN
    cW
    iswrdi
    3syl
    @2
    @8
    @11
    @1
    @8
    @11
    wi
    @0
    @14
    @1
    @11
    @8
    @1
    @14
    @11
    cW
    cN
    ffzo0hash
    expcom
    @4
    @5
    cW
    ffn
    syl11
    adantl
    imp
    jca
    ex
    syl5bir
    expcomd
    imp
    @2
    @16
    @14
    wi
    @12
    @2
    @9
    @11
    @14
    @9
    @2
    @11
    @14
    wi
    #
    @9
    cc0
    @10
    cfzo
    co
    #
    cV
    cW
    wf
    cW
    @21
    wfn
    #
    @2
    @20
    wi
    cV
    cW
    wrdf
    @21
    cV
    cW
    ffn
    @11
    @2
    @22
    @14
    @11
    @22
    @14
    wi
    @2
    @11
    @22
    @14
    @11
    @21
    @4
    cW
    @10
    cN
    cc0
    cfzo
    oveq2
    fneq2d
    biimpd
    a1d
    com13
    3syl
    com12
    impd
    adantr
    impbid
    ex
    pm5.32rd
    @17
    @9
    @11
    @12
    df-3an
    3bitr4g
    3bitr2d
end
