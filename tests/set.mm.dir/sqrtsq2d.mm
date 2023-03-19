include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wb.mm"
include "sqrtsq2.mm"
include "syl22anc.mm"

theorem sqrtsq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )
  assume sqr11d.3: |- ( ph -> B e. RR )
  assume sqr11d.4: |- ( ph -> 0 <_ B )


  assert |- ( ph -> ( ( sqrt ` A ) = B <-> A = ( B ^ 2 ) ) )

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
    csqrt
    cfv
    cB
    wceq
    cA
    cB
    c2
    cexp
    co
    wceq
    wb
    resqrcld.1
    resqrcld.2
    sqr11d.3
    sqr11d.4
    cA
    cB
    sqrtsq2
    syl22anc
end
