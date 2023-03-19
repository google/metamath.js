include "wcel.mm"
include "co.mm"
include "id.mm"
include "caovclg.mm"
include "syl12anc.mm"

theorem caovcld
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume caovclg.1: |- ( ( ph /\ ( x e. C /\ y e. D ) ) -> ( x F y ) e. E )
  assume caovcld.2: |- ( ph -> A e. C )
  assume caovcld.3: |- ( ph -> B e. D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint E x
  disjoint E y
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  assert |- ( ph -> ( A F B ) e. E )

  proof
    wph
    wph
    cA
    cC
    wcel
    cB
    cD
    wcel
    cA
    cB
    cF
    co
    cE
    wcel
    wph
    id
    caovcld.2
    caovcld.3
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cE
    cF
    caovclg.1
    caovclg
    syl12anc
end
