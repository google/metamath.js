include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wb.mm"
include "rpregt0d.mm"
include "ltmul2.mm"
include "syl3anc.mm"

theorem ltmul2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltmul1d.1: |- ( ph -> A e. RR )
  assume ltmul1d.2: |- ( ph -> B e. RR )
  assume ltmul1d.3: |- ( ph -> C e. RR+ )


  assert |- ( ph -> ( A < B <-> ( C x. A ) < ( C x. B ) ) )

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
    cB
    clt
    wbr
    cC
    cA
    cmul
    co
    cC
    cB
    cmul
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
    ltmul2
    syl3anc
end
