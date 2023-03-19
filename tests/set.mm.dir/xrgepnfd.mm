include "cpnf.mm"
include "cxr.mm"
include "wcel.mm"
include "pnfxr.mm"
include "a1i.mm"
include "cle.mm"
include "wbr.mm"
include "pnfge.mm"
include "syl.mm"
include "xrletrid.mm"

theorem xrgepnfd
  let wph: wff ph
  let cA: class A
  assume xrgepnfd.1: |- ( ph -> A e. RR* )
  assume xrgepnfd.2: |- ( ph -> +oo <_ A )


  assert |- ( ph -> A = +oo )

  proof
    wph
    cA
    cpnf
    xrgepnfd.1
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    wph
    cA
    cxr
    wcel
    cA
    cpnf
    cle
    wbr
    xrgepnfd.1
    cA
    pnfge
    syl
    xrgepnfd.2
    xrletrid
end
