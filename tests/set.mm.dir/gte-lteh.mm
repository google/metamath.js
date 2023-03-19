include "cge-real.mm"
include "wbr.mm"
include "cle.mm"
include "ccnv.mm"
include "df-gte.mm"
include "breqi.mm"
include "brcnv.mm"
include "bitri.mm"

theorem gte-lteh
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  assume gte-lteh.1: |- A e. _V
  assume gte-lteh.2: |- B e. _V


  assert |- ( A >_ B <-> B <_ A )

  proof
    cA
    cB
    cge-real
    wbr
    cA
    cB
    cle
    ccnv
    #
    wbr
    cB
    cA
    cle
    wbr
    cA
    cB
    cge-real
    @0
    df-gte
    breqi
    cA
    cB
    cle
    gte-lteh.1
    gte-lteh.2
    brcnv
    bitri
end
