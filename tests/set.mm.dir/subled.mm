include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "suble.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem subled
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume subled.4: |- ( ph -> ( A - B ) <_ C )


  assert |- ( ph -> ( A - C ) <_ B )

  proof
    wph
    cA
    cB
    cmin
    co
    cC
    cle
    wbr
    #
    cA
    cC
    cmin
    co
    cB
    cle
    wbr
    #
    subled.4
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cC
    cr
    wcel
    @0
    @1
    wb
    leidd.1
    ltnegd.2
    ltadd1d.3
    cA
    cB
    cC
    suble
    syl3anc
    mpbid
end
