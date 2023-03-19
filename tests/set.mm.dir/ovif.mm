include "cif.mm"
include "co.mm"
include "oveq1.mm"
include "ifsb.mm"

theorem ovif
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( if ( ph , A , B ) F C ) = if ( ph , ( A F C ) , ( B F C ) )

  proof
    wph
    cA
    cB
    wph
    cA
    cB
    cif
    #
    cC
    cF
    co
    cA
    cC
    cF
    co
    cB
    cC
    cF
    co
    @0
    cA
    cC
    cF
    oveq1
    @0
    cB
    cC
    cF
    oveq1
    ifsb
end
