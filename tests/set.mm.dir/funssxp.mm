include "wfun.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "cdm.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "funfn.mm"
include "biimpi.mm"
include "rnss.mm"
include "rnxpss.mm"
include "syl6ss.mm"
include "anim12i.mm"
include "df-f.mm"
include "sylibr.mm"
include "dmss.mm"
include "dmxpss.mm"
include "adantl.mm"
include "jca.mm"
include "ffun.mm"
include "adantr.mm"
include "fssxp.mm"
include "xpss1.mm"
include "sylan9ss.mm"
include "impbii.mm"

theorem funssxp
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ F C_ ( A X. B ) ) <-> ( F : dom F --> B /\ dom F C_ A ) )

  proof
    cF
    wfun
    #
    cF
    cA
    cB
    cxp
    #
    wss
    #
    wa
    #
    cF
    cdm
    #
    cB
    cF
    wf
    #
    @4
    cA
    wss
    #
    wa
    #
    @3
    @5
    @6
    @3
    cF
    @4
    wfn
    #
    cF
    crn
    #
    cB
    wss
    #
    wa
    @5
    @0
    @8
    @2
    @10
    @0
    @8
    cF
    funfn
    biimpi
    @2
    @9
    @1
    crn
    cB
    cF
    @1
    rnss
    cA
    cB
    rnxpss
    syl6ss
    anim12i
    @4
    cB
    cF
    df-f
    sylibr
    @2
    @6
    @0
    @2
    @4
    @1
    cdm
    cA
    cF
    @1
    dmss
    cA
    cB
    dmxpss
    syl6ss
    adantl
    jca
    @7
    @0
    @2
    @5
    @0
    @6
    @4
    cB
    cF
    ffun
    adantr
    @5
    @6
    cF
    @4
    cB
    cxp
    @1
    @4
    cB
    cF
    fssxp
    @4
    cA
    cB
    xpss1
    sylan9ss
    jca
    impbii
end
