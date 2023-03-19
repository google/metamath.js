include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cafv.mm"
include "cvv.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "ioran.mm"
include "wi.mm"
include "wne.mm"
include "df-ne.mm"
include "afvnufveq.mm"
include "sylbir.mm"
include "eqeq1.mm"
include "notbid.mm"
include "biimpd.mm"
include "syl.mm"
include "impcom.mm"
include "sylbi.mm"
include "con4i.mm"
include "afv0fv0.mm"
include "afvpcfv0.mm"
include "jaoi.mm"
include "impbii.mm"

theorem afvfv0bi
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F ` A ) = (/) <-> ( ( F ''' A ) = (/) \/ ( F ''' A ) = _V ) )

  proof
    cA
    cF
    cfv
    #
    c0
    wceq
    #
    cA
    cF
    cafv
    #
    c0
    wceq
    #
    @2
    cvv
    wceq
    #
    wo
    #
    @5
    @1
    @5
    wn
    @3
    wn
    #
    @4
    wn
    #
    wa
    @1
    wn
    #
    @3
    @4
    ioran
    @7
    @6
    @8
    @7
    @2
    @0
    wceq
    #
    @6
    @8
    wi
    @7
    @2
    cvv
    wne
    @9
    @2
    cvv
    df-ne
    cA
    cF
    afvnufveq
    sylbir
    @9
    @6
    @8
    @9
    @3
    @1
    @2
    @0
    c0
    eqeq1
    notbid
    biimpd
    syl
    impcom
    sylbi
    con4i
    @3
    @1
    @4
    cA
    cF
    afv0fv0
    cA
    cF
    afvpcfv0
    jaoi
    impbii
end
