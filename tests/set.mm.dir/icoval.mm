include "cle.mm"
include "clt.mm"
include "cico.mm"
include "df-ico.mm"
include "ixxval.mm"

theorem icoval
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
  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A [,) B ) = { x e. RR* | ( A <_ x /\ x < B ) } )

  proof
    vy
    vz
    vx
    cA
    cB
    cle
    clt
    cico
    vy
    vz
    vx
    df-ico
    ixxval
end
