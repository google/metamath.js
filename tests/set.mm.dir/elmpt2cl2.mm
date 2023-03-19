include "co.mm"
include "wcel.mm"
include "elmpt2cl.mm"
include "simprd.mm"

theorem elmpt2cl2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let vz: setvar z
  assume elmpt2cl.f: |- F = ( x e. A , y e. B |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint C z
  assert |- ( X e. ( S F T ) -> T e. B )

  proof
    cX
    cS
    cT
    cF
    co
    wcel
    cS
    cA
    wcel
    cT
    cB
    wcel
    vx
    vy
    cA
    cB
    cC
    cS
    cT
    cF
    cX
    elmpt2cl.f
    elmpt2cl
    simprd
end
