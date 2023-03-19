include "cc.mm"
include "wf.mm"
include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cpr.mm"
include "wcel.mm"
include "cres.mm"
include "wceq.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "simpl.mm"
include "ssid.mm"
include "simpr.mm"
include "dvres3.mm"
include "syl22anc.mm"

theorem dvcnre
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F : CC --> CC /\ RR C_ dom ( CC _D F ) ) -> ( RR _D ( F |` RR ) ) = ( ( CC _D F ) |` RR ) )

  proof
    cc
    cc
    cF
    wf
    #
    cr
    cc
    cF
    cdv
    co
    #
    cdm
    wss
    #
    wa
    #
    cr
    cr
    cc
    cpr
    wcel
    #
    @0
    cc
    cc
    wss
    #
    @2
    cr
    cF
    cr
    cres
    cdv
    co
    @1
    cr
    cres
    wceq
    @4
    @3
    reelprrecn
    a1i
    @0
    @2
    simpl
    @5
    @3
    cc
    ssid
    a1i
    @0
    @2
    simpr
    cc
    cr
    cF
    dvres3
    syl22anc
end
