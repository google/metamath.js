include "eqcomd.mm"
include "sylan9eq.mm"

theorem sylan9req
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume sylan9req.1: |- ( ph -> B = A )
  assume sylan9req.2: |- ( ps -> B = C )


  assert |- ( ( ph /\ ps ) -> A = C )

  proof
    wph
    wps
    cA
    cB
    cC
    wph
    cB
    cA
    sylan9req.1
    eqcomd
    sylan9req.2
    sylan9eq
end
