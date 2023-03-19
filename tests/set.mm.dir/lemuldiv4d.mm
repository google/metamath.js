include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "lemuldiv.mm"
include "syl112anc.mm"
include "bicomd.mm"
include "mpbid.mm"

theorem lemuldiv4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume lemuldiv4d.1: |- ( ph -> B <_ ( C / A ) )
  assume lemuldiv4d.2: |- ( ph -> 0 < A )
  assume lemuldiv4d.3: |- ( ph -> A e. RR )
  assume lemuldiv4d.4: |- ( ph -> B e. RR )
  assume lemuldiv4d.5: |- ( ph -> C e. RR )


  assert |- ( ph -> ( B x. A ) <_ C )

  proof
    wph
    cB
    cC
    cA
    cdiv
    co
    cle
    wbr
    #
    cB
    cA
    cmul
    co
    cC
    cle
    wbr
    #
    lemuldiv4d.1
    wph
    @1
    @0
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
    @1
    @0
    wb
    lemuldiv4d.4
    lemuldiv4d.5
    lemuldiv4d.3
    lemuldiv4d.2
    cB
    cC
    cA
    lemuldiv
    syl112anc
    bicomd
    mpbid
end
