include "nfcv.mm"
include "cbvitg.mm"

theorem cbvitgv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume cbvitg.1: |- ( x = y -> B = C )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint B k
  disjoint C k
  assert |- S. A B _d x = S. A C _d y

  proof
    vx
    vy
    cA
    cB
    cC
    cbvitg.1
    vy
    cB
    nfcv
    vx
    cC
    nfcv
    cbvitg
end
