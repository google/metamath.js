include "cxr.mm"
include "wcel.mm"
include "cxne.mm"
include "wceq.mm"
include "xnegneg.mm"
include "syl.mm"

theorem xnegnegd
  let wph: wff ph
  let cA: class A
  assume xnegnegd.1: |- ( ph -> A e. RR* )


  assert |- ( ph -> -e -e A = A )

  proof
    wph
    cA
    cxr
    wcel
    cA
    cxne
    cxne
    cA
    wceq
    xnegnegd.1
    cA
    xnegneg
    syl
end
