include "wceq.mm"
include "wb.mm"
include "eqeqan12d.mm"
include "ancoms.mm"

theorem eqeqan12rd
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eqeqan12rd.1: |- ( ph -> A = B )
  assume eqeqan12rd.2: |- ( ps -> C = D )


  assert |- ( ( ps /\ ph ) -> ( A = C <-> B = D ) )

  proof
    wph
    wps
    cA
    cC
    wceq
    cB
    cD
    wceq
    wb
    wph
    wps
    cA
    cB
    cC
    cD
    eqeqan12rd.1
    eqeqan12rd.2
    eqeqan12d
    ancoms
end
