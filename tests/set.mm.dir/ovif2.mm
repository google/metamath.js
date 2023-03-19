include "cif.mm"
include "co.mm"
include "oveq2.mm"
include "ifsb.mm"

theorem ovif2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A F if ( ph , B , C ) ) = if ( ph , ( A F B ) , ( A F C ) )

  proof
    wph
    cB
    cC
    cA
    wph
    cB
    cC
    cif
    #
    cF
    co
    cA
    cB
    cF
    co
    cA
    cC
    cF
    co
    @0
    cB
    cA
    cF
    oveq2
    @0
    cC
    cA
    cF
    oveq2
    ifsb
end
