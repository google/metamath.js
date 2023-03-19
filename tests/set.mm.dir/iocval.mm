include "clt.mm"
include "cle.mm"
include "cioc.mm"
include "df-ioc.mm"
include "ixxval.mm"

theorem iocval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D

  disjoint A x
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A (,] B ) = { x e. RR* | ( A < x /\ x <_ B ) } )

  proof
    vy
    vz
    vx
    cA
    cB
    clt
    cle
    cioc
    vy
    vz
    vx
    df-ioc
    ixxval
end
