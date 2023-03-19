include "wcel.mm"
include "csn.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "cz.mm"
include "1z.mm"
include "en2sn.mm"
include "mpan2.mm"
include "cfn.mm"
include "wb.mm"
include "snfi.mm"
include "hashen.mm"
include "mp2an.mm"
include "sylibr.mm"
include "cfz.mm"
include "co.mm"
include "cn0.mm"
include "1nn0.mm"
include "hashfz1.mm"
include "ax-mp.mm"
include "fzsn.mm"
include "fveq2d.mm"
include "syl5reqr.mm"
include "syl6eq.mm"

theorem hashsng
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( # ` { A } ) = 1 )

  proof
    cA
    cV
    wcel
    #
    cA
    csn
    #
    chash
    cfv
    #
    c1
    csn
    #
    chash
    cfv
    #
    c1
    @0
    @1
    @3
    cen
    wbr
    #
    @2
    @4
    wceq
    #
    @0
    c1
    cz
    wcel
    #
    @5
    1z
    cA
    c1
    cV
    cz
    en2sn
    mpan2
    @1
    cfn
    wcel
    @3
    cfn
    wcel
    @6
    @5
    wb
    cA
    snfi
    c1
    snfi
    @1
    @3
    hashen
    mp2an
    sylibr
    @7
    @4
    c1
    wceq
    1z
    @7
    c1
    c1
    c1
    cfz
    co
    #
    chash
    cfv
    #
    @4
    c1
    cn0
    wcel
    @9
    c1
    wceq
    1nn0
    c1
    hashfz1
    ax-mp
    @7
    @8
    @3
    chash
    c1
    fzsn
    fveq2d
    syl5reqr
    ax-mp
    syl6eq
end
