include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cle.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "rpregt0d.mm"
include "lerec.mm"
include "syl2anc.mm"

theorem lerecd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpred.1: |- ( ph -> A e. RR+ )
  assume rpaddcld.1: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( A <_ B <-> ( 1 / B ) <_ ( 1 / A ) ) )

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
    cA
    cB
    cle
    wbr
    c1
    cB
    cdiv
    co
    c1
    cA
    cdiv
    co
    cle
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
    cA
    cB
    lerec
    syl2anc
end
