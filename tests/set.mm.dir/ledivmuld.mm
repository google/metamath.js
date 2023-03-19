include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "cmul.mm"
include "wb.mm"
include "rpregt0d.mm"
include "ledivmul.mm"
include "syl3anc.mm"

theorem ledivmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltmul1d.1: |- ( ph -> A e. RR )
  assume ltmul1d.2: |- ( ph -> B e. RR )
  assume ltmul1d.3: |- ( ph -> C e. RR+ )


  assert |- ( ph -> ( ( A / C ) <_ B <-> A <_ ( C x. B ) ) )

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
    cdiv
    co
    cB
    cle
    wbr
    cA
    cC
    cB
    cmul
    co
    cle
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
    ledivmul
    syl3anc
end
