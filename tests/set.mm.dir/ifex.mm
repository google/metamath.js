include "cvv.mm"
include "keepel.mm"

theorem ifex
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume dedex.1: |- A e. _V
  assume dedex.2: |- B e. _V


  assert |- if ( ph , A , B ) e. _V

  proof
    wph
    cA
    cB
    cvv
    dedex.1
    dedex.2
    keepel
end
