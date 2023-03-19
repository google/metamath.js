include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "rpregt0d.mm"
include "ltdiv2.mm"
include "syl3anc.mm"

theorem ltdiv2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume rpred.1: |- ( ph -> A e. RR+ )
  assume rpaddcld.1: |- ( ph -> B e. RR+ )
  assume ltdiv2d.3: |- ( ph -> C e. RR+ )


  assert |- ( ph -> ( A < B <-> ( C / B ) < ( C / A ) ) )

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
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    wa
    cC
    cr
    wcel
    cc0
    cC
    clt
    wbr
    wa
    cA
    cB
    clt
    wbr
    cC
    cB
    cdiv
    co
    cC
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
    wph
    cB
    rpaddcld.1
    rpregt0d
    wph
    cC
    ltdiv2d.3
    rpregt0d
    cA
    cB
    cC
    ltdiv2
    syl3anc
end
