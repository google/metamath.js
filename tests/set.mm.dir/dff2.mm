include "wf.mm"
include "wfn.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "ffn.mm"
include "fssxp.mm"
include "jca.mm"
include "crn.mm"
include "rnss.mm"
include "rnxpss.mm"
include "syl6ss.mm"
include "anim2i.mm"
include "df-f.mm"
include "sylibr.mm"
include "impbii.mm"

theorem dff2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B <-> ( F Fn A /\ F C_ ( A X. B ) ) )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    cA
    wfn
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
    @0
    @1
    @3
    cA
    cB
    cF
    ffn
    cA
    cB
    cF
    fssxp
    jca
    @4
    @1
    cF
    crn
    #
    cB
    wss
    #
    wa
    @0
    @3
    @6
    @1
    @3
    @5
    @2
    crn
    cB
    cF
    @2
    rnss
    cA
    cB
    rnxpss
    syl6ss
    anim2i
    cA
    cB
    cF
    df-f
    sylibr
    impbii
end
