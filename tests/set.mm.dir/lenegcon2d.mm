include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "lenegcon2.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem lenegcon2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume lenegcon2d.3: |- ( ph -> A <_ -u B )


  assert |- ( ph -> B <_ -u A )

  proof
    wph
    cA
    cB
    cneg
    cle
    wbr
    #
    cB
    cA
    cneg
    cle
    wbr
    #
    lenegcon2d.3
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
    lenegcon2
    syl2anc
    mpbid
end
