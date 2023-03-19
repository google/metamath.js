include "cr.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "ctan.mm"
include "retancl.mm"
include "syl2anc.mm"

theorem retancld
  let wph: wff ph
  let cA: class A
  assume resincld.1: |- ( ph -> A e. RR )
  assume retancld.2: |- ( ph -> ( cos ` A ) =/= 0 )


  assert |- ( ph -> ( tan ` A ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cA
    ccos
    cfv
    cc0
    wne
    cA
    ctan
    cfv
    cr
    wcel
    resincld.1
    retancld.2
    cA
    retancl
    syl2anc
end
