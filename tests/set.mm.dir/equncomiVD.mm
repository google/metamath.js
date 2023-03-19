include "cun.mm"
include "wceq.mm"
include "equncom.mm"
include "biimpi.mm"
include "e0a.mm"

theorem equncomiVD
  let cA: class A
  let cB: class B
  let cC: class C
  assume equncomiVD.1: |- A = ( B u. C )


  assert |- A = ( C u. B )

  proof
    cA
    cB
    cC
    cun
    wceq
    #
    cA
    cC
    cB
    cun
    wceq
    #
    equncomiVD.1
    @0
    @1
    cA
    cB
    cC
    equncom
    biimpi
    e0a
end
