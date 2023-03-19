include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "wb.mm"
include "lenlt.mm"
include "syl2anc.mm"

theorem lenltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A <_ B <-> -. B < A ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cle
    wbr
    cB
    cA
    clt
    wbr
    wn
    wb
    ltd.1
    ltd.2
    cA
    cB
    lenlt
    syl2anc
end
