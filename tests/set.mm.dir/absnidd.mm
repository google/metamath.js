include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "cneg.mm"
include "wceq.mm"
include "absnid.mm"
include "syl2anc.mm"

theorem absnidd
  let wph: wff ph
  let cA: class A
  assume resqrcld.1: |- ( ph -> A e. RR )
  assume absnidd.2: |- ( ph -> A <_ 0 )


  assert |- ( ph -> ( abs ` A ) = -u A )

  proof
    wph
    cA
    cr
    wcel
    cA
    cc0
    cle
    wbr
    cA
    cabs
    cfv
    cA
    cneg
    wceq
    resqrcld.1
    absnidd.2
    cA
    absnid
    syl2anc
end
