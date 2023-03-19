include "cun.mm"
include "wceq.mm"
include "equncom.mm"
include "mpbi.mm"

theorem equncomi
  let cA: class A
  let cB: class B
  let cC: class C
  assume equncomi.1: |- A = ( B u. C )


  assert |- A = ( C u. B )

  proof
    cA
    cB
    cC
    cun
    wceq
    cA
    cC
    cB
    cun
    wceq
    equncomi.1
    cA
    cB
    cC
    equncom
    mpbi
end
