include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "wb.mm"
include "xrltnle.mm"
include "syl2anc.mm"

theorem xrltnled
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrltnled.1: |- ( ph -> A e. RR* )
  assume xrltnled.2: |- ( ph -> B e. RR* )


  assert |- ( ph -> ( A < B <-> -. B <_ A ) )

  proof
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    clt
    wbr
    cB
    cA
    cle
    wbr
    wn
    wb
    xrltnled.1
    xrltnled.2
    cA
    cB
    xrltnle
    syl2anc
end
