include "copab.mm"
include "co.mm"
include "wrel.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "relmpt2opab.mm"
include "a1i.mm"
include "brovex.mm"

theorem brovmpt2ex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cP: class P
  let cE: class E
  let cF: class F
  let cO: class O
  let cV: class V
  assume brovmpt2ex.1: |- O = ( x e. _V , y e. _V |-> { <. z , w >. | ph } )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( F ( V O E ) P -> ( ( V e. _V /\ E e. _V ) /\ ( F e. _V /\ P e. _V ) ) )

  proof
    vx
    vy
    wph
    vz
    vw
    copab
    cP
    cE
    cF
    cO
    cV
    brovmpt2ex.1
    cV
    cE
    cO
    co
    wrel
    cV
    cvv
    wcel
    cE
    cvv
    wcel
    wa
    wph
    vx
    vy
    vz
    vw
    cvv
    cvv
    cV
    cE
    cO
    brovmpt2ex.1
    relmpt2opab
    a1i
    brovex
end
