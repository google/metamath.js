include "wceq.mm"
include "caddc.mm"
include "co.mm"
include "cbc.mm"
include "oveq2.mm"
include "id.mm"
include "oveq12d.mm"

theorem bcxmaslem1
  let cA: class A
  let cB: class B
  let cN: class N
  let vj: setvar j
  let vm: setvar m
  let cM: class M
  let vk: setvar k


  assert |- ( A = B -> ( ( N + A ) _C A ) = ( ( N + B ) _C B ) )

  proof
    cA
    cB
    wceq
    #
    cN
    cA
    caddc
    co
    cN
    cB
    caddc
    co
    cA
    cB
    cbc
    cA
    cB
    cN
    caddc
    oveq2
    @0
    id
    oveq12d
end
