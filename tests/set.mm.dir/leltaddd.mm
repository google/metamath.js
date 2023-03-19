include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "leltadd.mm"
include "syl22anc.mm"
include "mp2and.mm"

theorem leltaddd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume lt2addd.4: |- ( ph -> D e. RR )
  assume leltaddd.5: |- ( ph -> A <_ C )
  assume leltaddd.6: |- ( ph -> B < D )


  assert |- ( ph -> ( A + B ) < ( C + D ) )

  proof
    wph
    cA
    cC
    cle
    wbr
    #
    cB
    cD
    clt
    wbr
    #
    cA
    cB
    caddc
    co
    cC
    cD
    caddc
    co
    clt
    wbr
    #
    leltaddd.5
    leltaddd.6
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
    cD
    cr
    wcel
    @0
    @1
    wa
    @2
    wi
    leidd.1
    ltnegd.2
    ltadd1d.3
    lt2addd.4
    cA
    cB
    cC
    cD
    leltadd
    syl22anc
    mp2and
end
