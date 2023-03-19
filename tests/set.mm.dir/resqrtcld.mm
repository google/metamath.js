include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "resqrtcl.mm"
include "syl2anc.mm"

theorem resqrtcld
  let wph: wff ph
  let cA: class A
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )


  assert |- ( ph -> ( sqrt ` A ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cA
    csqrt
    cfv
    cr
    wcel
    resqrcld.1
    resqrcld.2
    cA
    resqrtcl
    syl2anc
end
