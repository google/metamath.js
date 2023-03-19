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
include "ledivdiv.mm"
include "syl22anc.mm"
include "mpbid.mm"

theorem ledivdivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rpred.1: |- ( ph -> A e. RR+ )
  assume rpaddcld.1: |- ( ph -> B e. RR+ )
  assume ltdiv2d.3: |- ( ph -> C e. RR+ )
  assume ledivdivd.4: |- ( ph -> D e. RR+ )
  assume ledivdivd.5: |- ( ph -> ( A / B ) <_ ( C / D ) )


  assert |- ( ph -> ( D / C ) <_ ( B / A ) )

  proof
    wph
    cA
    cB
    cdiv
    co
    cC
    cD
    cdiv
    co
    cle
    wbr
    #
    cD
    cC
    cdiv
    co
    cB
    cA
    cdiv
    co
    cle
    wbr
    #
    ledivdivd.5
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
    cC
    cr
    wcel
    cc0
    cC
    clt
    wbr
    wa
    cD
    cr
    wcel
    cc0
    cD
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
    wph
    cC
    ltdiv2d.3
    rpregt0d
    wph
    cD
    ledivdivd.4
    rpregt0d
    cA
    cB
    cC
    cD
    ledivdiv
    syl22anc
    mpbid
end
