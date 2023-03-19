include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "csqrt.mm"
include "cfv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "sqrtneg.mm"
include "syl2anc.mm"

theorem sqrtnegd
  let wph: wff ph
  let cA: class A
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )


  assert |- ( ph -> ( sqrt ` -u A ) = ( _i x. ( sqrt ` A ) ) )

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
    cneg
    csqrt
    cfv
    ci
    cA
    csqrt
    cfv
    cmul
    co
    wceq
    resqrcld.1
    resqrcld.2
    cA
    sqrtneg
    syl2anc
end
