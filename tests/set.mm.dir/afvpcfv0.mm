include "cafv.mm"
include "cvv.mm"
include "wceq.mm"
include "wdfat.mm"
include "cfv.mm"
include "cif.mm"
include "c0.mm"
include "dfafv2.mm"
include "eqeq1i.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "eqcom.mm"
include "eqif.mm"
include "bitri.mm"
include "fveqvfvv.mm"
include "eqcoms.mm"
include "adantl.mm"
include "wne.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "fvfundmfvn0.mm"
include "df-dfat.mm"
include "sylibr.mm"
include "necon1bi.mm"
include "adantr.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem afvpcfv0
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F ''' A ) = _V -> ( F ` A ) = (/) )

  proof
    cA
    cF
    cafv
    #
    cvv
    wceq
    cA
    cF
    wdfat
    #
    cA
    cF
    cfv
    #
    cvv
    cif
    #
    cvv
    wceq
    #
    @2
    c0
    wceq
    #
    @0
    @3
    cvv
    cA
    cF
    dfafv2
    eqeq1i
    @4
    @1
    cvv
    @2
    wceq
    #
    wa
    #
    @1
    wn
    #
    cvv
    cvv
    wceq
    #
    wa
    #
    wo
    #
    @5
    @4
    cvv
    @3
    wceq
    @11
    @3
    cvv
    eqcom
    @1
    cvv
    @2
    cvv
    eqif
    bitri
    @7
    @5
    @10
    @6
    @5
    @1
    @5
    @2
    cvv
    cA
    c0
    cF
    fveqvfvv
    eqcoms
    adantl
    @8
    @5
    @9
    @1
    @2
    c0
    @2
    c0
    wne
    cA
    cF
    cdm
    wcel
    cF
    cA
    csn
    cres
    wfun
    wa
    @1
    cA
    cF
    fvfundmfvn0
    cA
    cF
    df-dfat
    sylibr
    necon1bi
    adantr
    jaoi
    sylbi
    sylbi
end
