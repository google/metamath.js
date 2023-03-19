include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "sqrt11.mm"
include "syl22anc.mm"
include "mpbid.mm"

theorem sqr11d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )
  assume sqr11d.3: |- ( ph -> B e. RR )
  assume sqr11d.4: |- ( ph -> 0 <_ B )
  assume sqrt11d.5: |- ( ph -> ( sqrt ` A ) = ( sqrt ` B ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    csqrt
    cfv
    cB
    csqrt
    cfv
    wceq
    #
    cA
    cB
    wceq
    #
    sqrt11d.5
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
    @0
    @1
    wb
    resqrcld.1
    resqrcld.2
    sqr11d.3
    sqr11d.4
    cA
    cB
    sqrt11
    syl22anc
    mpbid
end
