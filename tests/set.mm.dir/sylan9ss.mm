include "wss.mm"
include "sstr.mm"
include "syl2an.mm"

theorem sylan9ss
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume sylan9ss.1: |- ( ph -> A C_ B )
  assume sylan9ss.2: |- ( ps -> B C_ C )


  assert |- ( ( ph /\ ps ) -> A C_ C )

  proof
    wph
    cA
    cB
    wss
    cB
    cC
    wss
    cA
    cC
    wss
    wps
    sylan9ss.1
    sylan9ss.2
    cA
    cB
    cC
    sstr
    syl2an
end
