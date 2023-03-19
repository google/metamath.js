include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cmre.mm"
include "acsmre.mm"
include "syl.mm"

theorem acsmred
  let wph: wff ph
  let cA: class A
  let cX: class X
  assume acsmred.1: |- ( ph -> A e. ( ACS ` X ) )


  assert |- ( ph -> A e. ( Moore ` X ) )

  proof
    wph
    cA
    cX
    cacs
    cfv
    wcel
    cA
    cX
    cmre
    cfv
    wcel
    acsmred.1
    cA
    cX
    acsmre
    syl
end
