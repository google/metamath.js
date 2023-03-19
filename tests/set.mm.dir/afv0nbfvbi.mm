include "c0.mm"
include "wnel.mm"
include "cafv.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "afvvfveq.mm"
include "eleq1.mm"
include "biimpd.mm"
include "mpcom.mm"
include "wi.mm"
include "wa.mm"
include "wne.mm"
include "cdm.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "elnelne2.mm"
include "ancoms.mm"
include "fvfundmfvn0.mm"
include "wdfat.mm"
include "df-dfat.mm"
include "afvfundmfveq.mm"
include "sylbir.mm"
include "wb.mm"
include "eqcoms.mm"
include "4syl.mm"
include "ex.mm"
include "pm2.43d.mm"
include "impbid2.mm"

theorem afv0nbfvbi
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( (/) e/ B -> ( ( F ''' A ) e. B <-> ( F ` A ) e. B ) )

  proof
    c0
    cB
    wnel
    #
    cA
    cF
    cafv
    #
    cB
    wcel
    #
    cA
    cF
    cfv
    #
    cB
    wcel
    #
    @1
    @3
    wceq
    #
    @2
    @4
    cA
    cB
    cF
    afvvfveq
    @5
    @2
    @4
    @1
    @3
    cB
    eleq1
    biimpd
    mpcom
    @0
    @4
    @2
    @0
    @4
    @4
    @2
    wi
    #
    @0
    @4
    wa
    @3
    c0
    wne
    #
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
    #
    @5
    @6
    @4
    @0
    @7
    @3
    c0
    cB
    elnelne2
    ancoms
    cA
    cF
    fvfundmfvn0
    @8
    cA
    cF
    wdfat
    @5
    cA
    cF
    df-dfat
    cA
    cF
    afvfundmfveq
    sylbir
    @5
    @4
    @2
    @4
    @2
    wb
    @3
    @1
    @3
    @1
    cB
    eleq1
    eqcoms
    biimpd
    4syl
    ex
    pm2.43d
    impbid2
end
