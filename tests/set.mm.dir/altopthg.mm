include "caltop.mm"
include "wceq.mm"
include "csn.mm"
include "wa.mm"
include "wcel.mm"
include "altopthsn.mm"
include "sneqbg.mm"
include "bi2anan9.mm"
include "syl5bb.mm"

theorem altopthg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) ) )

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
    cD
    csn
    wceq
    #
    wa
    cA
    cV
    wcel
    #
    cB
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
    @2
    @0
    @4
    @3
    @1
    @5
    cA
    cC
    cV
    sneqbg
    cB
    cD
    cW
    sneqbg
    bi2anan9
    syl5bb
end
