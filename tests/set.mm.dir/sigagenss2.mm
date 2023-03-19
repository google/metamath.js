include "cuni.mm"
include "wceq.mm"
include "csigagen.mm"
include "cfv.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "csiga.mm"
include "sigagensiga.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "simp2.mm"
include "sigagenss.mm"
include "syl2anc.mm"

theorem sigagenss2
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( U. A = U. B /\ A C_ ( sigaGen ` B ) /\ B e. V ) -> ( sigaGen ` A ) C_ ( sigaGen ` B ) )

  proof
    cA
    cuni
    #
    cB
    cuni
    #
    wceq
    #
    cA
    cB
    csigagen
    cfv
    #
    wss
    #
    cB
    cV
    wcel
    #
    w3a
    #
    @3
    @0
    csiga
    cfv
    #
    wcel
    @4
    cA
    csigagen
    cfv
    @3
    wss
    @6
    @3
    @1
    csiga
    cfv
    #
    @7
    @5
    @2
    @3
    @8
    wcel
    @4
    cB
    cV
    sigagensiga
    3ad2ant3
    @6
    @0
    @1
    csiga
    @2
    @4
    @5
    simp1
    fveq2d
    eleqtrrd
    @2
    @4
    @5
    simp2
    cA
    @3
    sigagenss
    syl2anc
end
