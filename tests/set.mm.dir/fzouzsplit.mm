include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfzo.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "wo.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cr.mm"
include "eluzelre.mm"
include "lelttric.mm"
include "syl2an.mm"
include "orcomd.mm"
include "cz.mm"
include "wb.mm"
include "id.mm"
include "eluzelz.mm"
include "w3a.mm"
include "elfzo2.mm"
include "df-3an.mm"
include "bitri.mm"
include "baib.mm"
include "syl2anr.mm"
include "eluz.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "ex.mm"
include "elun.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "wss.mm"
include "elfzouz.mm"
include "ssriv.mm"
include "a1i.mm"
include "uzss.mm"
include "unssd.mm"
include "eqssd.mm"

theorem fzouzsplit
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cC: class C
  let cD: class D


  assert |- ( B e. ( ZZ>= ` A ) -> ( ZZ>= ` A ) = ( ( A ..^ B ) u. ( ZZ>= ` B ) ) )

  proof
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    @0
    cA
    cB
    cfzo
    co
    #
    cB
    cuz
    cfv
    #
    cun
    #
    @1
    vx
    @0
    @4
    @1
    vx
    cv
    #
    @0
    wcel
    #
    @5
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    wo
    #
    @5
    @4
    wcel
    @1
    @6
    @9
    @1
    @6
    wa
    #
    @9
    @5
    cB
    clt
    wbr
    #
    cB
    @5
    cle
    wbr
    #
    wo
    @10
    @12
    @11
    @1
    cB
    cr
    wcel
    @5
    cr
    wcel
    @12
    @11
    wo
    @6
    cA
    cB
    eluzelre
    cA
    @5
    eluzelre
    cB
    @5
    lelttric
    syl2an
    orcomd
    @10
    @7
    @11
    @8
    @12
    @6
    @6
    cB
    cz
    wcel
    #
    @7
    @11
    wb
    @1
    @6
    id
    cA
    cB
    eluzelz
    #
    @7
    @6
    @13
    wa
    #
    @11
    @7
    @6
    @13
    @11
    w3a
    @15
    @11
    wa
    @5
    cA
    cB
    elfzo2
    @6
    @13
    @11
    df-3an
    bitri
    baib
    syl2anr
    @1
    @13
    @5
    cz
    wcel
    @8
    @12
    wb
    @6
    @14
    cA
    @5
    eluzelz
    cB
    @5
    eluz
    syl2an
    orbi12d
    mpbird
    ex
    @5
    @2
    @3
    elun
    syl6ibr
    ssrdv
    @1
    @2
    @3
    @0
    @2
    @0
    wss
    @1
    vx
    @2
    @0
    @5
    cA
    cB
    elfzouz
    ssriv
    a1i
    cA
    cB
    uzss
    unssd
    eqssd
end
