include "wa.mm"
include "wceq.mm"
include "adantr.mm"
include "adantl.mm"
include "eqeq12d.mm"

theorem eqeqan12d
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eqeqan12d.1: |- ( ph -> A = B )
  assume eqeqan12d.2: |- ( ps -> C = D )


  assert |- ( ( ph /\ ps ) -> ( A = C <-> B = D ) )

  proof
    wph
    wps
    wa
    cA
    cB
    cC
    cD
    wph
    cA
    cB
    wceq
    wps
    eqeqan12d.1
    adantr
    wps
    cC
    cD
    wceq
    wph
    eqeqan12d.2
    adantl
    eqeq12d
end
