include "c0.mm"
include "wfn.mm"
include "wceq.mm"
include "wrel.mm"
include "cdm.mm"
include "fnrel.mm"
include "fndm.mm"
include "reldm0.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "wfun.mm"
include "fun0.mm"
include "dm0.mm"
include "df-fn.mm"
include "mpbir2an.mm"
include "fneq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem fn0
  let cF: class F


  assert |- ( F Fn (/) <-> F = (/) )

  proof
    cF
    c0
    wfn
    #
    cF
    c0
    wceq
    #
    @0
    cF
    wrel
    #
    cF
    cdm
    c0
    wceq
    #
    @1
    c0
    cF
    fnrel
    c0
    cF
    fndm
    @2
    @1
    @3
    cF
    reldm0
    biimpar
    syl2anc
    @1
    @0
    c0
    c0
    wfn
    #
    @4
    c0
    wfun
    c0
    cdm
    c0
    wceq
    fun0
    dm0
    c0
    c0
    df-fn
    mpbir2an
    c0
    cF
    c0
    fneq1
    mpbiri
    impbii
end
