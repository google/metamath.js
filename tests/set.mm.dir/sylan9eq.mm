include "wceq.mm"
include "eqtr.mm"
include "syl2an.mm"

theorem sylan9eq
  param wph: wff ph
  param wps: wff ps
  param cA: class A
  param cB: class B
  param cC: class C
  assume sylan9eq.1: |- ( ph -> A = B )
  assume sylan9eq.2: |- ( ps -> B = C )


  assert |- ( ( ph /\ ps ) -> A = C )

  proof
    wph
    cA
    cB
    wceq
    cB
    cC
    wceq
    cA
    cC
    wceq
    wps
    sylan9eq.1
    sylan9eq.2
    cA
    cB
    cC
    eqtr
    syl2an
end
