include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "cif.mm"
include "csn.mm"
include "cuni.mm"
include "wceq.mm"
include "iftrue.mm"
include "unisng.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "snprc.mm"
include "biimpi.mm"
include "unieqd.mm"
include "uni0.mm"
include "syl6eq.mm"
include "pm2.61i.mm"
include "eqcomi.mm"

theorem unisnif
  let cA: class A


  assert |- U. { A } = if ( A e. _V , A , (/) )

  proof
    cA
    cvv
    wcel
    #
    cA
    c0
    cif
    #
    cA
    csn
    #
    cuni
    #
    @0
    @1
    @3
    wceq
    @0
    @1
    cA
    @3
    @0
    cA
    c0
    iftrue
    cA
    cvv
    unisng
    eqtr4d
    @0
    wn
    #
    @1
    c0
    @3
    @0
    cA
    c0
    iffalse
    @4
    @3
    c0
    cuni
    c0
    @4
    @2
    c0
    @4
    @2
    c0
    wceq
    cA
    snprc
    biimpi
    unieqd
    uni0
    syl6eq
    eqtr4d
    pm2.61i
    eqcomi
end
