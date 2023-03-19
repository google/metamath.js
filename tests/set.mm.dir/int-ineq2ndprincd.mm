include "lemul1ad.mm"

theorem int-ineq2ndprincd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume int-ineq2ndprincd.1: |- ( ph -> A e. RR )
  assume int-ineq2ndprincd.2: |- ( ph -> B e. RR )
  assume int-ineq2ndprincd.3: |- ( ph -> C e. RR )
  assume int-ineq2ndprincd.4: |- ( ph -> B <_ A )
  assume int-ineq2ndprincd.5: |- ( ph -> 0 <_ C )


  assert |- ( ph -> ( B x. C ) <_ ( A x. C ) )

  proof
    wph
    cB
    cA
    cC
    int-ineq2ndprincd.2
    int-ineq2ndprincd.1
    int-ineq2ndprincd.3
    int-ineq2ndprincd.5
    int-ineq2ndprincd.4
    lemul1ad
end
