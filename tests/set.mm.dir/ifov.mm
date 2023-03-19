include "cif.mm"
include "co.mm"
include "oveq.mm"
include "ifsb.mm"

theorem ifov
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( A if ( ph , F , G ) B ) = if ( ph , ( A F B ) , ( A G B ) )

  proof
    wph
    cF
    cG
    cA
    cB
    wph
    cF
    cG
    cif
    #
    co
    cA
    cB
    cF
    co
    cA
    cB
    cG
    co
    cA
    cB
    @0
    cF
    oveq
    cA
    cB
    @0
    cG
    oveq
    ifsb
end
