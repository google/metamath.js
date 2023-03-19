include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "rpred.mm"
include "rpgt0d.mm"
include "ge0div.mm"
include "syl3anc.mm"

theorem ge0divd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpgecld.1: |- ( ph -> A e. RR )
  assume rpgecld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( 0 <_ A <-> 0 <_ ( A / B ) ) )

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
    cle
    wbr
    cc0
    cA
    cB
    cdiv
    co
    cle
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
    ge0div
    syl3anc
end
