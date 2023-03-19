include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wa.mm"
include "wb.mm"
include "rpregt0d.mm"
include "ltrec1.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem ltrec1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpred.1: |- ( ph -> A e. RR+ )
  assume rpaddcld.1: |- ( ph -> B e. RR+ )
  assume ltrec1d.2: |- ( ph -> ( 1 / A ) < B )


  assert |- ( ph -> ( 1 / B ) < A )

  proof
    wph
    c1
    cA
    cdiv
    co
    cB
    clt
    wbr
    #
    c1
    cB
    cdiv
    co
    cA
    clt
    wbr
    #
    ltrec1d.2
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
    ltrec1
    syl2anc
    mpbid
end
