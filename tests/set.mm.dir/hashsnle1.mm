include "csn.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "wo.mm"
include "cle.mm"
include "wbr.mm"
include "hashsn01.mm"
include "0le1.mm"
include "breq1.mm"
include "mpbiri.mm"
include "1le1.mm"
include "jaoi.mm"
include "ax-mp.mm"

theorem hashsnle1
  let cA: class A


  assert |- ( # ` { A } ) <_ 1

  proof
    cA
    csn
    chash
    cfv
    #
    cc0
    wceq
    #
    @0
    c1
    wceq
    #
    wo
    @0
    c1
    cle
    wbr
    #
    cA
    hashsn01
    @1
    @3
    @2
    @1
    @3
    cc0
    c1
    cle
    wbr
    0le1
    @0
    cc0
    c1
    cle
    breq1
    mpbiri
    @2
    @3
    c1
    c1
    cle
    wbr
    1le1
    @0
    c1
    c1
    cle
    breq1
    mpbiri
    jaoi
    ax-mp
end
