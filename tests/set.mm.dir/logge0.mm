include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "clog.mm"
include "cfv.mm"
include "log1.mm"
include "simpr.mm"
include "crp.mm"
include "wb.mm"
include "1rp.mm"
include "rpgecl.mm"
include "mp3an1.mm"
include "logleb.mm"
include "sylancr.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"

theorem logge0
  let cA: class A


  assert |- ( ( A e. RR /\ 1 <_ A ) -> 0 <_ ( log ` A ) )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    wa
    #
    cc0
    c1
    clog
    cfv
    #
    cA
    clog
    cfv
    #
    cle
    log1
    @2
    @1
    @3
    @4
    cle
    wbr
    #
    @0
    @1
    simpr
    @2
    c1
    crp
    wcel
    #
    cA
    crp
    wcel
    #
    @1
    @5
    wb
    1rp
    @6
    @0
    @1
    @7
    1rp
    c1
    cA
    rpgecl
    mp3an1
    c1
    cA
    logleb
    sylancr
    mpbid
    syl5eqbrr
end
