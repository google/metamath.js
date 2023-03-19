include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cxne.mm"
include "wb.mm"
include "xnegre.mm"
include "syl.mm"

theorem xnegred
  let wph: wff ph
  let cA: class A
  assume xnegred.1: |- ( ph -> A e. RR* )


  assert |- ( ph -> ( A e. RR <-> -e A e. RR ) )

  proof
    wph
    cA
    cxr
    wcel
    cA
    cr
    wcel
    cA
    cxne
    cr
    wcel
    wb
    xnegred.1
    cA
    xnegre
    syl
end
