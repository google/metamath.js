include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "sqrtge0.mm"
include "syl2anc.mm"

theorem sqrtge0d
  let wph: wff ph
  let cA: class A
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )


  assert |- ( ph -> 0 <_ ( sqrt ` A ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cc0
    cA
    csqrt
    cfv
    cle
    wbr
    resqrcld.1
    resqrcld.2
    cA
    sqrtge0
    syl2anc
end
