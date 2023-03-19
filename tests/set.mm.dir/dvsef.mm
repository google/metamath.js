include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "ce.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "wss.mm"
include "cdm.mm"
include "wceq.mm"
include "eff.mm"
include "jctr.mm"
include "recnprss.mm"
include "dvef.mm"
include "dmeqi.mm"
include "fdmi.mm"
include "eqtri.mm"
include "syl6sseqr.mm"
include "ssid.mm"
include "jctil.mm"
include "dvres3.mm"
include "syl2anc.mm"
include "reseq1i.mm"
include "syl6eq.mm"

theorem dvsef
  let cS: class S


  assert |- ( S e. { RR , CC } -> ( S _D ( exp |` S ) ) = ( exp |` S ) )

  proof
    cS
    cr
    cc
    cpr
    wcel
    #
    cS
    ce
    cS
    cres
    #
    cdv
    co
    #
    cc
    ce
    cdv
    co
    #
    cS
    cres
    #
    @1
    @0
    @0
    cc
    cc
    ce
    wf
    #
    wa
    cc
    cc
    wss
    #
    cS
    @3
    cdm
    #
    wss
    #
    wa
    @2
    @4
    wceq
    @0
    @5
    eff
    jctr
    @0
    @8
    @6
    @0
    cS
    cc
    @7
    cS
    recnprss
    @7
    ce
    cdm
    cc
    @3
    ce
    dvef
    dmeqi
    cc
    cc
    ce
    eff
    fdmi
    eqtri
    syl6sseqr
    cc
    ssid
    jctil
    cc
    cS
    ce
    dvres3
    syl2anc
    @3
    ce
    cS
    dvef
    reseq1i
    syl6eq
end
