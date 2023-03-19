include "wcel.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cxp.mm"
include "cvv.mm"
include "dmexg.mm"
include "rnexg.mm"
include "unexg.mm"
include "syl2anc.mm"
include "sqxpexg.mm"
include "syl.mm"
include "mpdan.mm"

theorem rtrclexlem
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R u. ( ( dom R u. ran R ) X. ( dom R u. ran R ) ) ) e. _V )

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
    cun
    #
    @3
    cxp
    #
    cvv
    wcel
    #
    cR
    @4
    cun
    cvv
    wcel
    @0
    @3
    cvv
    wcel
    #
    @5
    @0
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @6
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
    unexg
    syl2anc
    @3
    cvv
    sqxpexg
    syl
    cR
    @4
    cV
    cvv
    unexg
    mpdan
end
