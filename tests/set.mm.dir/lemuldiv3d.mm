include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "lemuldiv.mm"
include "syl112anc.mm"
include "mpbid.mm"

theorem lemuldiv3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume lemuldiv3d.1: |- ( ph -> ( B x. A ) <_ C )
  assume lemuldiv3d.2: |- ( ph -> 0 < A )
  assume lemuldiv3d.3: |- ( ph -> A e. RR )
  assume lemuldiv3d.4: |- ( ph -> B e. RR )
  assume lemuldiv3d.5: |- ( ph -> C e. RR )


  assert |- ( ph -> B <_ ( C / A ) )

  proof
    wph
    cB
    cA
    cmul
    co
    cC
    cle
    wbr
    #
    cB
    cC
    cA
    cdiv
    co
    cle
    wbr
    #
    lemuldiv3d.1
    wph
    cB
    cr
    wcel
    cC
    cr
    wcel
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    @0
    @1
    wb
    lemuldiv3d.4
    lemuldiv3d.5
    lemuldiv3d.3
    lemuldiv3d.2
    cB
    cC
    cA
    lemuldiv
    syl112anc
    mpbid
end
