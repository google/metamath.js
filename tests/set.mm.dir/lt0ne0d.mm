include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "wceq.mm"
include "0re.mm"
include "ltnri.mm"
include "breq1.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "syl.mm"

theorem lt0ne0d
  let wph: wff ph
  let cA: class A
  assume lt0ne0d.1: |- ( ph -> A < 0 )


  assert |- ( ph -> A =/= 0 )

  proof
    wph
    cA
    cc0
    clt
    wbr
    #
    cA
    cc0
    wne
    lt0ne0d.1
    @0
    cA
    cc0
    cA
    cc0
    wceq
    @0
    cc0
    cc0
    clt
    wbr
    cc0
    0re
    ltnri
    cA
    cc0
    cc0
    clt
    breq1
    mtbiri
    necon2ai
    syl
end
