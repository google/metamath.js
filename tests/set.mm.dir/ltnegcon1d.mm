include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "ltnegcon1.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem ltnegcon1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltnegcon1d.3: |- ( ph -> -u A < B )


  assert |- ( ph -> -u B < A )

  proof
    wph
    cA
    cneg
    cB
    clt
    wbr
    #
    cB
    cneg
    cA
    clt
    wbr
    #
    ltnegcon1d.3
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
    ltnegcon1
    syl2anc
    mpbid
end
