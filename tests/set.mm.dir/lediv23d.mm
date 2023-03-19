include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wa.mm"
include "wb.mm"
include "rpregt0d.mm"
include "lediv23.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem lediv23d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltdiv23d.1: |- ( ph -> A e. RR )
  assume ltdiv23d.2: |- ( ph -> B e. RR+ )
  assume ltdiv23d.3: |- ( ph -> C e. RR+ )
  assume lediv23d.4: |- ( ph -> ( A / B ) <_ C )


  assert |- ( ph -> ( A / C ) <_ B )

  proof
    wph
    cA
    cB
    cdiv
    co
    cC
    cle
    wbr
    #
    cA
    cC
    cdiv
    co
    cB
    cle
    wbr
    #
    lediv23d.4
    wph
    cA
    cr
    wcel
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
    @0
    @1
    wb
    ltdiv23d.1
    wph
    cB
    ltdiv23d.2
    rpregt0d
    wph
    cC
    ltdiv23d.3
    rpregt0d
    cA
    cB
    cC
    lediv23
    syl3anc
    mpbid
end
