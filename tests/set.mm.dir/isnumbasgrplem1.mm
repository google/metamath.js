include "cen.mm"
include "wbr.mm"
include "cabl.mm"
include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cbs.mm"
include "cima.mm"
include "ensymb.mm"
include "bren.mm"
include "bitri.mm"
include "wi.mm"
include "wa.mm"
include "cimas.mm"
include "co.mm"
include "cfv.mm"
include "eqidd.mm"
include "wceq.mm"
include "a1i.mm"
include "wfo.mm"
include "f1ofo.mm"
include "adantr.mm"
include "simpr.mm"
include "imasbas.mm"
include "cgim.mm"
include "cgic.mm"
include "wb.mm"
include "simpl.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "adantl.mm"
include "imasgim.mm"
include "brgici.mm"
include "gicabl.mm"
include "3syl.mm"
include "mpbid.mm"
include "cvv.mm"
include "wfn.mm"
include "wss.mm"
include "basfn.mm"
include "ssv.mm"
include "fnfvima.mm"
include "mp3an12.mm"
include "syl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "exlimiv.mm"
include "impcom.mm"
include "sylan2b.mm"

theorem isnumbasgrplem1
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  assume isnumbasgrplem1.b: |- B = ( Base ` R )


  assert |- ( ( R e. Abel /\ C ~~ B ) -> C e. ( Base " Abel ) )

  proof
    cC
    cB
    cen
    wbr
    #
    cR
    cabl
    wcel
    #
    cB
    cC
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    cC
    cbs
    cabl
    cima
    #
    wcel
    #
    @0
    cB
    cC
    cen
    wbr
    @4
    cC
    cB
    ensymb
    cB
    cC
    vf
    bren
    bitri
    @4
    @1
    @6
    @3
    @1
    @6
    wi
    vf
    @3
    @1
    @6
    @3
    @1
    wa
    #
    cC
    @2
    cR
    cimas
    co
    #
    cbs
    cfv
    #
    @5
    @7
    cC
    cR
    @8
    @2
    cB
    cabl
    @7
    @8
    eqidd
    #
    cB
    cR
    cbs
    cfv
    wceq
    @7
    isnumbasgrplem1.b
    a1i
    #
    @3
    cB
    cC
    @2
    wfo
    @1
    cB
    cC
    @2
    f1ofo
    adantr
    @3
    @1
    simpr
    #
    imasbas
    @7
    @8
    cabl
    wcel
    #
    @9
    @5
    wcel
    #
    @7
    @1
    @13
    @12
    @7
    @2
    cR
    @8
    cgim
    co
    wcel
    cR
    @8
    cgic
    wbr
    @1
    @13
    wb
    @7
    cC
    cR
    @8
    @2
    cB
    @10
    @11
    @3
    @1
    simpl
    @1
    cR
    cgrp
    wcel
    @3
    cR
    ablgrp
    adantl
    imasgim
    cR
    @8
    @2
    brgici
    cR
    @8
    gicabl
    3syl
    mpbid
    cbs
    cvv
    wfn
    cabl
    cvv
    wss
    @13
    @14
    basfn
    cabl
    ssv
    cvv
    cabl
    cbs
    @8
    fnfvima
    mp3an12
    syl
    eqeltrd
    ex
    exlimiv
    impcom
    sylan2b
end
