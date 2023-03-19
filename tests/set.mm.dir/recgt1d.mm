include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "rpregt0d.mm"
include "recgt1.mm"
include "syl.mm"

theorem recgt1d
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( 1 < A <-> ( 1 / A ) < 1 ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    wa
    c1
    cA
    clt
    wbr
    c1
    cA
    cdiv
    co
    c1
    clt
    wbr
    wb
    wph
    cA
    rpred.1
    rpregt0d
    cA
    recgt1
    syl
end
