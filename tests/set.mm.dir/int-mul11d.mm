include "c1.mm"
include "cmul.mm"
include "co.mm"
include "recnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"

theorem int-mul11d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume int-mul11d.1: |- ( ph -> A e. RR )
  assume int-mul11d.2: |- ( ph -> A = B )


  assert |- ( ph -> ( A x. 1 ) = B )

  proof
    wph
    cA
    c1
    cmul
    co
    cA
    cB
    wph
    cA
    wph
    cA
    int-mul11d.1
    recnd
    mulid1d
    int-mul11d.2
    eqtrd
end
