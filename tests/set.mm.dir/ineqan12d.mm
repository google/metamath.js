include "wceq.mm"
include "cin.mm"
include "ineq12.mm"
include "syl2an.mm"

theorem ineqan12d
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ineq1d.1: |- ( ph -> A = B )
  assume ineqan12d.2: |- ( ps -> C = D )


  assert |- ( ( ph /\ ps ) -> ( A i^i C ) = ( B i^i D ) )

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
    cin
    cB
    cD
    cin
    wceq
    wps
    ineq1d.1
    ineqan12d.2
    cA
    cB
    cC
    cD
    ineq12
    syl2an
end
