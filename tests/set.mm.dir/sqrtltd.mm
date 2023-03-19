include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "csqrt.mm"
include "cfv.mm"
include "wb.mm"
include "sqrtlt.mm"
include "syl22anc.mm"

theorem sqrtltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )
  assume sqr11d.3: |- ( ph -> B e. RR )
  assume sqr11d.4: |- ( ph -> 0 <_ B )


  assert |- ( ph -> ( A < B <-> ( sqrt ` A ) < ( sqrt ` B ) ) )

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
    clt
    wbr
    cA
    csqrt
    cfv
    cB
    csqrt
    cfv
    clt
    wbr
    wb
    resqrcld.1
    resqrcld.2
    sqr11d.3
    sqr11d.4
    cA
    cB
    sqrtlt
    syl22anc
end
