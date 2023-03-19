include "wcel.mm"
include "cif.mm"
include "eleq1.mm"
include "keephyp.mm"

theorem keepel
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume keepel.1: |- A e. C
  assume keepel.2: |- B e. C


  assert |- if ( ph , A , B ) e. C

  proof
    wph
    cA
    cC
    wcel
    cB
    cC
    wcel
    wph
    cA
    cB
    cif
    #
    cC
    wcel
    cA
    cB
    cA
    @0
    cC
    eleq1
    cB
    @0
    cC
    eleq1
    keepel.1
    keepel.2
    keephyp
end
