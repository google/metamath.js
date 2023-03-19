include "cxr.mm"
include "wcel.mm"
include "cxne.mm"
include "xnegcl.mm"
include "syl.mm"

theorem xnegcld
  let wph: wff ph
  let cA: class A
  assume xnegcld.1: |- ( ph -> A e. RR* )


  assert |- ( ph -> -e A e. RR* )

  proof
    wph
    cA
    cxr
    wcel
    cA
    cxne
    cxr
    wcel
    xnegcld.1
    cA
    xnegcl
    syl
end
