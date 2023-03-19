include "cfv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "c0v.mm"
include "wne.mm"
include "wa.mm"
include "csp.mm"
include "ccj.mm"
include "cr.mm"
include "wcel.mm"
include "cmul.mm"
include "oveq2.mm"
include "cc.mm"
include "chil.mm"
include "his5.mm"
include "mp3an.mm"
include "syl6eq.mm"
include "oveq1.mm"
include "ax-his3.mm"
include "eqeq12d.mm"
include "cc0.mm"
include "wb.mm"
include "hicli.mm"
include "clt.mm"
include "wbr.mm"
include "ax-his4.mm"
include "mpan.mm"
include "gt0ne0d.mm"
include "cjcli.mm"
include "mulcan2.mm"
include "mp3an12.mm"
include "sylancr.mm"
include "sylan9bb.mm"
include "cjrebi.mm"
include "syl6bbr.mm"

theorem eigrei
  let cA: class A
  let cB: class B
  let cT: class T
  assume eigre.1: |- A e. ~H
  assume eigre.2: |- B e. CC


  assert |- ( ( ( T ` A ) = ( B .h A ) /\ A =/= 0h ) -> ( ( A .ih ( T ` A ) ) = ( ( T ` A ) .ih A ) <-> B e. RR ) )

  proof
    cA
    cT
    cfv
    #
    cB
    cA
    csm
    co
    #
    wceq
    #
    cA
    c0v
    wne
    #
    wa
    cA
    @0
    csp
    co
    #
    @0
    cA
    csp
    co
    #
    wceq
    #
    cB
    ccj
    cfv
    #
    cB
    wceq
    #
    cB
    cr
    wcel
    @2
    @6
    @7
    cA
    cA
    csp
    co
    #
    cmul
    co
    #
    cB
    @9
    cmul
    co
    #
    wceq
    #
    @3
    @8
    @2
    @4
    @10
    @5
    @11
    @2
    @4
    cA
    @1
    csp
    co
    #
    @10
    @0
    @1
    cA
    csp
    oveq2
    cB
    cc
    wcel
    #
    cA
    chil
    wcel
    #
    @15
    @13
    @10
    wceq
    eigre.2
    eigre.1
    eigre.1
    cB
    cA
    cA
    his5
    mp3an
    syl6eq
    @2
    @5
    @1
    cA
    csp
    co
    #
    @11
    @0
    @1
    cA
    csp
    oveq1
    @14
    @15
    @15
    @16
    @11
    wceq
    eigre.2
    eigre.1
    eigre.1
    cB
    cA
    cA
    ax-his3
    mp3an
    syl6eq
    eqeq12d
    @3
    @9
    cc
    wcel
    #
    @9
    cc0
    wne
    #
    @12
    @8
    wb
    #
    cA
    cA
    eigre.1
    eigre.1
    hicli
    @3
    @9
    @15
    @3
    cc0
    @9
    clt
    wbr
    eigre.1
    cA
    ax-his4
    mpan
    gt0ne0d
    @7
    cc
    wcel
    @14
    @17
    @18
    wa
    @19
    cB
    eigre.2
    cjcli
    eigre.2
    @7
    cB
    @9
    mulcan2
    mp3an12
    sylancr
    sylan9bb
    cB
    eigre.2
    cjrebi
    syl6bbr
end
