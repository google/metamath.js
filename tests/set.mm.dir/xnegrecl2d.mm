include "cxr.mm"
include "wcel.mm"
include "cxne.mm"
include "cr.mm"
include "xnegrecl2.mm"
include "syl2anc.mm"

theorem xnegrecl2d
  let wph: wff ph
  let cA: class A
  assume xnegrecl2d.1: |- ( ph -> A e. RR* )
  assume xnegrecl2d.2: |- ( ph -> -e A e. RR )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cA
    cxr
    wcel
    cA
    cxne
    cr
    wcel
    cA
    cr
    wcel
    xnegrecl2d.1
    xnegrecl2d.2
    cA
    xnegrecl2
    syl2anc
end
