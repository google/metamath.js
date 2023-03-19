include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wb.mm"
include "rpregt0d.mm"
include "ltmuldiv.mm"
include "syl3anc.mm"

theorem ltmuldivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltmul1d.1: |- ( ph -> A e. RR )
  assume ltmul1d.2: |- ( ph -> B e. RR )
  assume ltmul1d.3: |- ( ph -> C e. RR+ )


  assert |- ( ph -> ( ( A x. C ) < B <-> A < ( B / C ) ) )

  proof
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
    cc0
    cC
    clt
    wbr
    wa
    cA
    cC
    cmul
    co
    cB
    clt
    wbr
    cA
    cB
    cC
    cdiv
    co
    clt
    wbr
    wb
    ltmul1d.1
    ltmul1d.2
    wph
    cC
    ltmul1d.3
    rpregt0d
    cA
    cB
    cC
    ltmuldiv
    syl3anc
end
