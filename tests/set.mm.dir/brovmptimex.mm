include "co.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "breqdi.mm"
include "brne0.mm"
include "reldmmpt2.mm"
include "ovprc.mm"
include "necon1ai.mm"
include "3syl.mm"

theorem brovmptimex
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
  assert |- ( ph -> ( C e. _V /\ D e. _V ) )

  proof
    wph
    cA
    cB
    cC
    cD
    cF
    co
    #
    wbr
    @0
    c0
    wne
    cC
    cvv
    wcel
    cD
    cvv
    wcel
    wa
    #
    wph
    cR
    @0
    cA
    cB
    brovmptimex.ov
    brovmptimex.br
    breqdi
    cA
    cB
    @0
    brne0
    @1
    @0
    c0
    cC
    cD
    cF
    vx
    vy
    cE
    cG
    cH
    cF
    brovmptimex.mpt
    reldmmpt2
    ovprc
    necon1ai
    3syl
end
