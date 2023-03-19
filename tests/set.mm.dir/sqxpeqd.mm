include "xpeq12d.mm"

theorem sqxpeqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xpeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A X. A ) = ( B X. B ) )

  proof
    wph
    cA
    cB
    cA
    cB
    xpeq1d.1
    xpeq1d.1
    xpeq12d
end
