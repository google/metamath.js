include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "sqrtmul.mm"
include "syl22anc.mm"

theorem sqrtmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )
  assume sqr11d.3: |- ( ph -> B e. RR )
  assume sqr11d.4: |- ( ph -> 0 <_ B )


  assert |- ( ph -> ( sqrt ` ( A x. B ) ) = ( ( sqrt ` A ) x. ( sqrt ` B ) ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cA
    cB
    cmul
    co
    csqrt
    cfv
    cA
    csqrt
    cfv
    cB
    csqrt
    cfv
    cmul
    co
    wceq
    resqrcld.1
    resqrcld.2
    sqr11d.3
    sqr11d.4
    cA
    cB
    sqrtmul
    syl22anc
end
