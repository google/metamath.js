include "nfcv.mm"
include "nfv.mm"
include "ovmpt2df.mm"

theorem ovmpt2dv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cV: class V
  assume ovmpt2df.1: |- ( ph -> A e. C )
  assume ovmpt2df.2: |- ( ( ph /\ x = A ) -> B e. D )
  assume ovmpt2df.3: |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V )
  assume ovmpt2df.4: |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ( A F B ) = R -> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint ps x
  disjoint ps y
  assert |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ps ) )

  proof
    wph
    wps
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    cF
    cV
    ovmpt2df.1
    ovmpt2df.2
    ovmpt2df.3
    ovmpt2df.4
    vx
    cF
    nfcv
    wps
    vx
    nfv
    vy
    cF
    nfcv
    wps
    vy
    nfv
    ovmpt2df
end
