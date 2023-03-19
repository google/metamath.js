include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "wo.mm"
include "hashsng.mm"
include "olcd.mm"
include "wn.mm"
include "c0.mm"
include "snprc.mm"
include "biimpi.mm"
include "fveq2d.mm"
include "hash0.mm"
include "syl6eq.mm"
include "orcd.mm"
include "pm2.61i.mm"

theorem hashsn01
  let cA: class A


  assert |- ( ( # ` { A } ) = 0 \/ ( # ` { A } ) = 1 )

  proof
    cA
    cvv
    wcel
    #
    cA
    csn
    #
    chash
    cfv
    #
    cc0
    wceq
    #
    @2
    c1
    wceq
    #
    wo
    @0
    @4
    @3
    cA
    cvv
    hashsng
    olcd
    @0
    wn
    #
    @3
    @4
    @5
    @2
    c0
    chash
    cfv
    cc0
    @5
    @1
    c0
    chash
    @5
    @1
    c0
    wceq
    cA
    snprc
    biimpi
    fveq2d
    hash0
    syl6eq
    orcd
    pm2.61i
end
