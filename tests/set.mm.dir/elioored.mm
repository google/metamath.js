include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "elioore.mm"
include "syl.mm"

theorem elioored
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume elioored.1: |- ( ph -> A e. ( B (,) C ) )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cA
    cB
    cC
    cioo
    co
    wcel
    cA
    cr
    wcel
    elioored.1
    cA
    cB
    cC
    elioore
    syl
end
