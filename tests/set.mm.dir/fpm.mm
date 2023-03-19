include "cvv.mm"
include "wcel.mm"
include "wf.mm"
include "cpm.mm"
include "co.mm"
include "fpmg.mm"
include "mp3an12.mm"

theorem fpm
  let cA: class A
  let cB: class B
  let cF: class F
  let vg: setvar g
  let vf: setvar f
  assume elmap.1: |- A e. _V
  assume elmap.2: |- B e. _V


  assert |- ( F : A --> B -> F e. ( B ^pm A ) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cF
    wf
    cF
    cB
    cA
    cpm
    co
    wcel
    elmap.1
    elmap.2
    cA
    cB
    cF
    cvv
    cvv
    fpmg
    mp3an12
end
