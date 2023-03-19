include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "recnd.mm"
include "addid1d.mm"
include "eqtrd.mm"

theorem int-add01d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume int-add01d.1: |- ( ph -> A e. RR )
  assume int-add01d.2: |- ( ph -> A = B )


  assert |- ( ph -> ( A + 0 ) = B )

  proof
    wph
    cA
    cc0
    caddc
    co
    cA
    cB
    wph
    cA
    wph
    cA
    int-add01d.1
    recnd
    addid1d
    int-add01d.2
    eqtrd
end
