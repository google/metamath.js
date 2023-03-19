include "word.mm"
include "ciun.mm"
include "iunord.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "mprg.mm"

theorem iunordi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume iunordi.B: |- Ord B

  disjoint A x
  disjoint k x
  assert |- Ord U_ x e. A B

  proof
    cB
    word
    #
    vx
    cA
    cB
    ciun
    word
    vx
    cA
    vx
    cA
    cB
    iunord
    @0
    vx
    cv
    cA
    wcel
    iunordi.B
    a1i
    mprg
end
