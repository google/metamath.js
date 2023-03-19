include "cclwwlk.mm"
include "cfv.mm"
include "wcel.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "cpr.mm"
include "cedg.mm"
include "cvtx.mm"
include "cword.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "isclwwlk.mm"
include "lsw1.mm"
include "preq1d.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "ex.mm"
include "com23.mm"
include "adantr.mm"
include "imp.mm"
include "3adant2.mm"
include "sylbi.mm"

theorem clwwlk1loop
  let cG: class G
  let cW: class W
  let vi: setvar i


  assert |- ( ( W e. ( ClWWalks ` G ) /\ ( # ` W ) = 1 ) -> { ( W ` 0 ) , ( W ` 0 ) } e. ( Edg ` G ) )

  proof
    cW
    cG
    cclwwlk
    cfv
    wcel
    #
    cW
    chash
    cfv
    #
    c1
    wceq
    #
    cc0
    cW
    cfv
    #
    @3
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    @0
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    cW
    c0
    wne
    #
    wa
    #
    vi
    cv
    #
    cW
    cfv
    @11
    c1
    caddc
    co
    cW
    cfv
    cpr
    @5
    wcel
    vi
    cc0
    @1
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    cW
    clsw
    cfv
    #
    @3
    cpr
    #
    @5
    wcel
    #
    w3a
    @2
    @6
    wi
    #
    vi
    @5
    cG
    @7
    cW
    @7
    eqid
    @5
    eqid
    isclwwlk
    @10
    @15
    @16
    @12
    @10
    @15
    @16
    @8
    @15
    @16
    wi
    @9
    @8
    @2
    @15
    @6
    @8
    @2
    @15
    @6
    wi
    @8
    @2
    wa
    #
    @15
    @6
    @17
    @14
    @4
    @5
    @17
    @13
    @3
    @3
    @7
    cW
    lsw1
    preq1d
    eleq1d
    biimpd
    ex
    com23
    adantr
    imp
    3adant2
    sylbi
    imp
end
