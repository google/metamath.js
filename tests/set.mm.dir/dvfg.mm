include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cperf.mm"
include "cdv.mm"
include "cdm.mm"
include "wf.mm"
include "eqid.mm"
include "recnperf.mm"
include "perfdvf.mm"
include "syl.mm"

theorem dvfg
  let cS: class S
  let cF: class F


  assert |- ( S e. { RR , CC } -> ( S _D F ) : dom ( S _D F ) --> CC )

  proof
    cS
    cr
    cc
    cpr
    wcel
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    cperf
    wcel
    cS
    cF
    cdv
    co
    #
    cdm
    cc
    @1
    wf
    cS
    @0
    @0
    eqid
    #
    recnperf
    cS
    cF
    @0
    @2
    perfdvf
    syl
end
