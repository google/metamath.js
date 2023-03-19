include "omlsi.mm"

theorem pjomli
  let cA: class A
  let cB: class B
  assume pjoml.1: |- A e. CH
  assume pjoml.2: |- B e. SH


  assert |- ( ( A C_ B /\ ( B i^i ( _|_ ` A ) ) = 0H ) -> A = B )

  proof
    cA
    cB
    pjoml.1
    pjoml.2
    omlsi
end
