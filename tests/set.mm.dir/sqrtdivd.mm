include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "cdiv.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "sqrtdiv.mm"
include "syl21anc.mm"

theorem sqrtdivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )
  assume sqrdivd.3: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( sqrt ` ( A / B ) ) = ( ( sqrt ` A ) / ( sqrt ` B ) ) )

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
    crp
    wcel
    cA
    cB
    cdiv
    co
    csqrt
    cfv
    cA
    csqrt
    cfv
    cB
    csqrt
    cfv
    cdiv
    co
    wceq
    resqrcld.1
    resqrcld.2
    sqrdivd.3
    cA
    cB
    sqrtdiv
    syl21anc
end
