include "wss.mm"
include "sylan9ss.mm"
include "ancoms.mm"

theorem sylan9ssr
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume sylan9ssr.1: |- ( ph -> A C_ B )
  assume sylan9ssr.2: |- ( ps -> B C_ C )


  assert |- ( ( ps /\ ph ) -> A C_ C )

  proof
    wph
    wps
    cA
    cC
    wss
    wph
    wps
    cA
    cB
    cC
    sylan9ssr.1
    sylan9ssr.2
    sylan9ss
    ancoms
end
