include "wceq.mm"
include "wb.mm"
include "eqeq12.mm"
include "syl2an.mm"

theorem eqeqan12dALT
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
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    wceq
    cB
    cD
    wceq
    wb
    wps
    eqeqan12d.1
    eqeqan12d.2
    cA
    cB
    cC
    cD
    eqeq12
    syl2an
end
