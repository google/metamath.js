include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cle.mm"
include "wbr.mm"
include "pnfge.mm"
include "syl.mm"

theorem pnfged
  let wph: wff ph
  let cA: class A
  assume pnfged.1: |- ( ph -> A e. RR* )


  assert |- ( ph -> A <_ +oo )

  proof
    wph
    cA
    cxr
    wcel
    cA
    cpnf
    cle
    wbr
    pnfged.1
    cA
    pnfge
    syl
end
