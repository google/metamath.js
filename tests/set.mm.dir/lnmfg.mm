include "clnm.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "clfig.mm"
include "eqid.mm"
include "ressid.mm"
include "clss.mm"
include "clmod.mm"
include "lnmlmod.mm"
include "lss1.mm"
include "syl.mm"
include "lnmlssfg.mm"
include "mpdan.mm"
include "eqeltrrd.mm"

theorem lnmfg
  let cM: class M
  let va: setvar a
  let cU: class U
  let cS: class S
  let cR: class R


  assert |- ( M e. LNoeM -> M e. LFinGen )

  proof
    cM
    clnm
    wcel
    #
    cM
    cM
    cbs
    cfv
    #
    cress
    co
    #
    cM
    clfig
    @1
    cM
    clnm
    @1
    eqid
    #
    ressid
    @0
    @1
    cM
    clss
    cfv
    #
    wcel
    #
    @2
    clfig
    wcel
    @0
    cM
    clmod
    wcel
    @5
    cM
    lnmlmod
    @4
    @1
    cM
    @3
    @4
    eqid
    #
    lss1
    syl
    @2
    @4
    @1
    cM
    @6
    @2
    eqid
    lnmlssfg
    mpdan
    eqeltrrd
end
