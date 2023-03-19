include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "lenegcon1.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem lenegcon1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume lenegcon1d.3: |- ( ph -> -u A <_ B )


  assert |- ( ph -> -u B <_ A )

  proof
    wph
    cA
    cneg
    cB
    cle
    wbr
    #
    cB
    cneg
    cA
    cle
    wbr
    #
    lenegcon1d.3
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @0
    @1
    wb
    leidd.1
    ltnegd.2
    cA
    cB
    lenegcon1
    syl2anc
    mpbid
end
