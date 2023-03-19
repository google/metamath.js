include "cdif.mm"
include "wcel.mm"
include "eldifn.mm"
include "con2i.mm"

theorem elndif
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. B -> -. A e. ( C \ B ) )

  proof
    cA
    cC
    cB
    cdif
    wcel
    cA
    cB
    wcel
    cA
    cC
    cB
    eldifn
    con2i
end
