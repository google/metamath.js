include "le2addd.mm"

theorem int-ineq1stprincd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume int-ineq1stprincd.1: |- ( ph -> A e. RR )
  assume int-ineq1stprincd.2: |- ( ph -> B e. RR )
  assume int-ineq1stprincd.3: |- ( ph -> C e. RR )
  assume int-ineq1stprincd.4: |- ( ph -> D e. RR )
  assume int-ineq1stprincd.5: |- ( ph -> B <_ A )
  assume int-ineq1stprincd.6: |- ( ph -> D <_ C )


  assert |- ( ph -> ( B + D ) <_ ( A + C ) )

  proof
    wph
    cB
    cD
    cA
    cC
    int-ineq1stprincd.2
    int-ineq1stprincd.4
    int-ineq1stprincd.1
    int-ineq1stprincd.3
    int-ineq1stprincd.5
    int-ineq1stprincd.6
    le2addd
end
