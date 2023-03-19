include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "0re.mm"
include "ltne.mm"
include "sylancr.mm"

theorem gt0ne0d
  let wph: wff ph
  let cA: class A
  assume gt0ne0d.1: |- ( ph -> 0 < A )


  assert |- ( ph -> A =/= 0 )

  proof
    wph
    cc0
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cA
    cc0
    wne
    0re
    gt0ne0d.1
    cc0
    cA
    ltne
    sylancr
end
