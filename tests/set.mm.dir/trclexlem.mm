include "wcel.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cvv.mm"
include "cun.mm"
include "dmexg.mm"
include "rnexg.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "unexg.mm"
include "mpdan.mm"

theorem trclexlem
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R u. ( dom R X. ran R ) ) e. _V )

  proof
    cR
    cV
    wcel
    #
    cR
    cdm
    #
    cR
    crn
    #
    cxp
    #
    cvv
    wcel
    #
    cR
    @3
    cun
    cvv
    wcel
    @0
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @4
    cR
    cV
    dmexg
    cR
    cV
    rnexg
    @1
    @2
    cvv
    cvv
    xpexg
    syl2anc
    cR
    @3
    cV
    cvv
    unexg
    mpdan
end
