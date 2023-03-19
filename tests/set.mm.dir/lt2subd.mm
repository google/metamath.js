include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "lt2sub.mm"
include "syl22anc.mm"
include "mp2and.mm"

theorem lt2subd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume lt2addd.4: |- ( ph -> D e. RR )
  assume lt2addd.5: |- ( ph -> A < C )
  assume lt2addd.6: |- ( ph -> B < D )


  assert |- ( ph -> ( A - D ) < ( C - B ) )

  proof
    wph
    cA
    cC
    clt
    wbr
    #
    cB
    cD
    clt
    wbr
    #
    cA
    cD
    cmin
    co
    cC
    cB
    cmin
    co
    clt
    wbr
    #
    lt2addd.5
    lt2addd.6
    wph
    cA
    cr
    wcel
    cD
    cr
    wcel
    cC
    cr
    wcel
    cB
    cr
    wcel
    @0
    @1
    wa
    @2
    wi
    leidd.1
    lt2addd.4
    ltadd1d.3
    ltnegd.2
    cA
    cD
    cC
    cB
    lt2sub
    syl22anc
    mp2and
end
