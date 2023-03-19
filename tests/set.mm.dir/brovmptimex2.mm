include "cvv.mm"
include "wcel.mm"
include "brovmptimex.mm"
include "simprd.mm"

theorem brovmptimex2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  assume brovmptimex.mpt: |- F = ( x e. E , y e. G |-> H )
  assume brovmptimex.br: |- ( ph -> A R B )
  assume brovmptimex.ov: |- ( ph -> R = ( C F D ) )

  disjoint E x
  disjoint E y
  disjoint x y
  disjoint F y
  assert |- ( ph -> D e. _V )

  proof
    wph
    cC
    cvv
    wcel
    cD
    cvv
    wcel
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    cE
    cF
    cG
    cH
    brovmptimex.mpt
    brovmptimex.br
    brovmptimex.ov
    brovmptimex
    simprd
end
