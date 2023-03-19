include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "lesub.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem lesubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume lesubd.4: |- ( ph -> A <_ ( B - C ) )


  assert |- ( ph -> C <_ ( B - A ) )

  proof
    wph
    cA
    cB
    cC
    cmin
    co
    cle
    wbr
    #
    cC
    cB
    cA
    cmin
    co
    cle
    wbr
    #
    lesubd.4
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
    lesub
    syl3anc
    mpbid
end
