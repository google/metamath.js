include "wceq.mm"
include "id.mm"
include "eqidd.mm"
include "afveq12d.mm"

theorem afveq1
  let cA: class A
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x


  assert |- ( F = G -> ( F ''' A ) = ( G ''' A ) )

  proof
    cF
    cG
    wceq
    #
    cA
    cA
    cF
    cG
    @0
    id
    @0
    cA
    eqidd
    afveq12d
end
