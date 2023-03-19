include "c1.mm"
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
include "lerec2.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem lerec2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpred.1: |- ( ph -> A e. RR+ )
  assume rpaddcld.1: |- ( ph -> B e. RR+ )
  assume lerec2d.2: |- ( ph -> A <_ ( 1 / B ) )


  assert |- ( ph -> B <_ ( 1 / A ) )

  proof
    wph
    cA
    c1
    cB
    cdiv
    co
    cle
    wbr
    #
    cB
    c1
    cA
    cdiv
    co
    cle
    wbr
    #
    lerec2d.2
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
    @0
    @1
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
    lerec2
    syl2anc
    mpbid
end
