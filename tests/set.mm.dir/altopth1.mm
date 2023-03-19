include "caltop.mm"
include "wceq.mm"
include "csn.mm"
include "wa.mm"
include "wcel.mm"
include "altopthsn.mm"
include "sneqrg.mm"
include "adantrd.mm"
include "syl5bi.mm"

theorem altopth1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( A e. V -> ( << A , B >> = << C , D >> -> A = C ) )

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
    cA
    cC
    wceq
    #
    cA
    cB
    cC
    cD
    altopthsn
    @2
    @0
    @3
    @1
    cA
    cC
    cV
    sneqrg
    adantrd
    syl5bi
end
