include "wcel.mm"
include "wral.mm"
include "ciin.mm"
include "wb.mm"
include "eliin.mm"
include "syl.mm"
include "mpbid.mm"
include "rspcva.mm"
include "syl2anc.mm"

theorem eliind
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cK: class K
  assume eliind.a: |- ( ph -> A e. |^|_ x e. B C )
  assume eliind.k: |- ( ph -> K e. B )
  assume eliind.d: |- ( x = K -> ( A e. C <-> A e. D ) )

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint K x
  assert |- ( ph -> A e. D )

  proof
    wph
    cK
    cB
    wcel
    cA
    cC
    wcel
    #
    vx
    cB
    wral
    #
    cA
    cD
    wcel
    #
    eliind.k
    wph
    cA
    vx
    cB
    cC
    ciin
    #
    wcel
    #
    @1
    eliind.a
    wph
    @4
    @4
    @1
    wb
    eliind.a
    vx
    cA
    cB
    cC
    @3
    eliin
    syl
    mpbid
    @0
    @2
    vx
    cK
    cB
    eliind.d
    rspcva
    syl2anc
end
