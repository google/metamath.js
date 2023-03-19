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
include "reclt1.mm"
include "syl.mm"

theorem reclt1d
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( A < 1 <-> 1 < ( 1 / A ) ) )

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
    cA
    c1
    clt
    wbr
    c1
    c1
    cA
    cdiv
    co
    clt
    wbr
    wb
    wph
    cA
    rpred.1
    rpregt0d
    cA
    reclt1
    syl
end
