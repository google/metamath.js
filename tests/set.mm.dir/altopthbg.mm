include "caltop.mm"
include "wceq.mm"
include "csn.mm"
include "wa.mm"
include "wcel.mm"
include "altopthsn.mm"
include "sneqbg.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "bi2anan9.mm"
include "syl5bb.mm"

theorem altopthbg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ D e. W ) -> ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) ) )

  proof
    cA
    cB
    caltop
    cC
    cD
    caltop
    wceq
    cA
    csn
    cC
    csn
    wceq
    #
    cB
    csn
    #
    cD
    csn
    #
    wceq
    #
    wa
    cA
    cV
    wcel
    #
    cD
    cW
    wcel
    #
    wa
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    cA
    cB
    cC
    cD
    altopthsn
    @4
    @0
    @6
    @5
    @3
    @7
    cA
    cC
    cV
    sneqbg
    @5
    @2
    @1
    wceq
    cD
    cB
    wceq
    @3
    @7
    cD
    cB
    cW
    sneqbg
    @1
    @2
    eqcom
    cB
    cD
    eqcom
    3bitr4g
    bi2anan9
    syl5bb
end
