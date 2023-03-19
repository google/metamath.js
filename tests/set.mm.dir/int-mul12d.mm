include "c1.mm"
include "cmul.mm"
include "co.mm"
include "recnd.mm"
include "mulid2d.mm"
include "eqtrd.mm"

theorem int-mul12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume int-mul12d.1: |- ( ph -> A e. RR )
  assume int-mul12d.2: |- ( ph -> A = B )


  assert |- ( ph -> ( 1 x. A ) = B )

  proof
    wph
    c1
    cA
    cmul
    co
    cA
    cB
    wph
    cA
    wph
    cA
    int-mul12d.1
    recnd
    mulid2d
    int-mul12d.2
    eqtrd
end
