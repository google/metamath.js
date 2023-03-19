include "wceq.mm"
include "eqidd.mm"
include "id.mm"
include "afveq12d.mm"

theorem afveq2
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( A = B -> ( F ''' A ) = ( F ''' B ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cB
    cF
    cF
    @0
    cF
    eqidd
    @0
    id
    afveq12d
end
