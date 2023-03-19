include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "absid.mm"
include "syl2anc.mm"

theorem absidd
  let wph: wff ph
  let cA: class A
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume resqrcld.2: |- ( ph -> 0 <_ A )


  assert |- ( ph -> ( abs ` A ) = A )

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
    cabs
    cfv
    cA
    wceq
    resqrcld.1
    resqrcld.2
    cA
    absid
    syl2anc
end
