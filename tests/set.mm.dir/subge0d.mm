include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "subge0.mm"
include "syl2anc.mm"

theorem subge0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( 0 <_ ( A - B ) <-> B <_ A ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cA
    cB
    cmin
    co
    cle
    wbr
    cB
    cA
    cle
    wbr
    wb
    leidd.1
    ltnegd.2
    cA
    cB
    subge0
    syl2anc
end
