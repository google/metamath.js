include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "recnd.mm"
include "addid2d.mm"
include "eqtrd.mm"

theorem int-add02d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume int-add02d.1: |- ( ph -> A e. RR )
  assume int-add02d.2: |- ( ph -> A = B )


  assert |- ( ph -> ( 0 + A ) = B )

  proof
    wph
    cc0
    cA
    caddc
    co
    cA
    cB
    wph
    cA
    wph
    cA
    int-add02d.1
    recnd
    addid2d
    int-add02d.2
    eqtrd
end
