include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "rpred.mm"
include "rpgt0d.mm"
include "gt0div.mm"
include "syl3anc.mm"

theorem gt0divd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpgecld.1: |- ( ph -> A e. RR )
  assume rpgecld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( 0 < A <-> 0 < ( A / B ) ) )

  proof
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
    cc0
    cA
    clt
    wbr
    cc0
    cA
    cB
    cdiv
    co
    clt
    wbr
    wb
    rpgecld.1
    wph
    cB
    rpgecld.2
    rpred
    wph
    cB
    rpgecld.2
    rpgt0d
    cA
    cB
    gt0div
    syl3anc
end
