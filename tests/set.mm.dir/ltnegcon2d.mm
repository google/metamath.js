include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "ltnegcon2.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem ltnegcon2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltnegcon2d.3: |- ( ph -> A < -u B )


  assert |- ( ph -> B < -u A )

  proof
    wph
    cA
    cB
    cneg
    clt
    wbr
    #
    cB
    cA
    cneg
    clt
    wbr
    #
    ltnegcon2d.3
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
    ltnegcon2
    syl2anc
    mpbid
end
