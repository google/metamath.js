include "wceq.mm"
include "c0.mm"
include "wcel.mm"
include "wne.mm"
include "wo.mm"
include "wa.mm"
include "wb.mm"
include "cpr.mm"
include "cif.mm"
include "eleq2.mm"
include "bibi1d.mm"
include "wn.mm"
include "noel.mm"
include "a1i.mm"
include "simpl.mm"
include "neneqd.mm"
include "simpr.mm"
include "nsyl3.mm"
include "2falsed.mm"
include "elprg.mm"
include "df-ne.mm"
include "ibar.mm"
include "sylbir.mm"
include "sylan9bb.mm"
include "ifbothda.mm"

theorem eupth2lem1
  let cA: class A
  let cB: class B
  let cU: class U
  let cV: class V


  assert |- ( U e. V -> ( U e. if ( A = B , (/) , { A , B } ) <-> ( A =/= B /\ ( U = A \/ U = B ) ) ) )

  proof
    cA
    cB
    wceq
    #
    cU
    c0
    wcel
    #
    cA
    cB
    wne
    #
    cU
    cA
    wceq
    cU
    cB
    wceq
    wo
    #
    wa
    #
    wb
    cU
    cA
    cB
    cpr
    #
    wcel
    #
    @4
    wb
    cU
    @0
    c0
    @5
    cif
    #
    wcel
    #
    @4
    wb
    cU
    cV
    wcel
    #
    c0
    @5
    c0
    @7
    wceq
    @1
    @8
    @4
    c0
    @7
    cU
    eleq2
    bibi1d
    @5
    @7
    wceq
    @6
    @8
    @4
    @5
    @7
    cU
    eleq2
    bibi1d
    @9
    @0
    wa
    #
    @1
    @4
    @1
    wn
    @10
    cU
    noel
    a1i
    @4
    @0
    @10
    @4
    cA
    cB
    @2
    @3
    simpl
    neneqd
    @9
    @0
    simpr
    nsyl3
    2falsed
    @9
    @6
    @3
    @0
    wn
    #
    @4
    cU
    cA
    cB
    cV
    elprg
    @11
    @2
    @3
    @4
    wb
    cA
    cB
    df-ne
    @2
    @3
    ibar
    sylbir
    sylan9bb
    ifbothda
end
