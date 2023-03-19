include "caltop.mm"
include "wceq.mm"
include "csn.mm"
include "wa.mm"
include "wcel.mm"
include "altopthsn.mm"
include "sneqrg.mm"
include "adantld.mm"
include "syl5bi.mm"

theorem altopth2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( B e. V -> ( << A , B >> = << C , D >> -> B = D ) )

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
    cB
    cV
    wcel
    #
    cB
    cD
    wceq
    #
    cA
    cB
    cC
    cD
    altopthsn
    @2
    @1
    @3
    @0
    cB
    cD
    cV
    sneqrg
    adantld
    syl5bi
end
