include "cfn.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "cn0.mm"
include "hashcl.mm"
include "hashfz1.mm"
include "syl.mm"
include "wb.mm"
include "fzfi.mm"
include "hashen.mm"
include "mpan.mm"
include "mpbid.mm"
include "ensym.mm"
include "enfi.mm"
include "biimprcd.mm"
include "mpsyl.mm"
include "impbii.mm"

theorem isfinite4
  let cA: class A


  assert |- ( A e. Fin <-> ( 1 ... ( # ` A ) ) ~~ A )

  proof
    cA
    cfn
    wcel
    #
    c1
    cA
    chash
    cfv
    #
    cfz
    co
    #
    cA
    cen
    wbr
    #
    @0
    @2
    chash
    cfv
    @1
    wceq
    #
    @3
    @0
    @1
    cn0
    wcel
    @4
    cA
    hashcl
    @1
    hashfz1
    syl
    @2
    cfn
    wcel
    #
    @0
    @4
    @3
    wb
    c1
    @1
    fzfi
    #
    @2
    cA
    hashen
    mpan
    mpbid
    @5
    @3
    cA
    @2
    cen
    wbr
    #
    @0
    @6
    @2
    cA
    ensym
    @7
    @0
    @5
    cA
    @2
    enfi
    biimprcd
    mpsyl
    impbii
end
