include "cv.mm"
include "wcel.mm"
include "crn.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"

theorem elrnmpt1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  assume elrnmpt1d.1: |- F = ( x e. A |-> B )
  assume elrnmpt1d.2: |- ( ph -> x e. A )
  assume elrnmpt1d.3: |- ( ph -> B e. V )


  assert |- ( ph -> B e. ran F )

  proof
    wph
    vx
    cv
    cA
    wcel
    cB
    cV
    wcel
    cB
    cF
    crn
    wcel
    elrnmpt1d.2
    elrnmpt1d.3
    vx
    cA
    cB
    cF
    cV
    elrnmpt1d.1
    elrnmpt1
    syl2anc
end
