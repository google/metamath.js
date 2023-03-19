include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cz.mm"
include "wb.mm"
include "cneg.mm"
include "wi.mm"
include "eleq1.mm"
include "bicomd.mm"
include "a1i.mm"
include "cc.mm"
include "recn.mm"
include "znegclb.mm"
include "syl.mm"
include "bibi2d.mm"
include "syl5ibrcom.mm"
include "absor.mm"
include "mpjaod.mm"

theorem absz
  let cA: class A


  assert |- ( A e. RR -> ( A e. ZZ <-> ( abs ` A ) e. ZZ ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cabs
    cfv
    #
    cA
    wceq
    #
    cA
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    wb
    #
    @1
    cA
    cneg
    #
    wceq
    #
    @2
    @5
    wi
    @0
    @2
    @4
    @3
    @1
    cA
    cz
    eleq1
    bicomd
    a1i
    @0
    @5
    @7
    @3
    @6
    cz
    wcel
    #
    wb
    #
    @0
    cA
    cc
    wcel
    @9
    cA
    recn
    cA
    znegclb
    syl
    @7
    @4
    @8
    @3
    @1
    @6
    cz
    eleq1
    bibi2d
    syl5ibrcom
    cA
    absor
    mpjaod
end
