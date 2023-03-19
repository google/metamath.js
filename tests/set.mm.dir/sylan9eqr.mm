include "wceq.mm"
include "sylan9eq.mm"
include "ancoms.mm"

theorem sylan9eqr
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume sylan9eqr.1: |- ( ph -> A = B )
  assume sylan9eqr.2: |- ( ps -> B = C )


  assert |- ( ( ps /\ ph ) -> A = C )

  proof
    wph
    wps
    cA
    cC
    wceq
    wph
    wps
    cA
    cB
    cC
    sylan9eqr.1
    sylan9eqr.2
    sylan9eq
    ancoms
end
