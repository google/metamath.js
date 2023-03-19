include "wrel.mm"
include "cdm.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "df-rel.mm"
include "anbi2i.mm"
include "crn.mm"
include "relssdmrn.mm"
include "ssv.mm"
include "xpss12.mm"
include "mpan2.mm"
include "sylan9ss.mm"
include "xpss.mm"
include "sstr.mm"
include "sylibr.mm"
include "dmss.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "vn0.mm"
include "dmxp.mm"
include "ax-mp.mm"
include "syl6sseq.mm"
include "jca.mm"
include "impbii.mm"
include "bitri.mm"

theorem relrelss
  let cA: class A


  assert |- ( ( Rel A /\ Rel dom A ) <-> A C_ ( ( _V X. _V ) X. _V ) )

  proof
    cA
    wrel
    #
    cA
    cdm
    #
    wrel
    #
    wa
    @0
    @1
    cvv
    cvv
    cxp
    #
    wss
    #
    wa
    #
    cA
    @3
    cvv
    cxp
    #
    wss
    #
    @2
    @4
    @0
    @1
    df-rel
    anbi2i
    @5
    @7
    @0
    @4
    cA
    @1
    cA
    crn
    #
    cxp
    #
    @6
    cA
    relssdmrn
    @4
    @8
    cvv
    wss
    @9
    @6
    wss
    @8
    ssv
    @1
    @3
    @8
    cvv
    xpss12
    mpan2
    sylan9ss
    @7
    @0
    @4
    @7
    cA
    @3
    wss
    #
    @0
    @7
    @6
    @3
    wss
    @10
    @3
    cvv
    xpss
    cA
    @6
    @3
    sstr
    mpan2
    cA
    df-rel
    sylibr
    @7
    @1
    @6
    cdm
    #
    @3
    cA
    @6
    dmss
    cvv
    c0
    wne
    @11
    @3
    wceq
    vn0
    @3
    cvv
    dmxp
    ax-mp
    syl6sseq
    jca
    impbii
    bitri
end
