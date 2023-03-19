include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "wss.mm"
include "cpolN.mm"
include "cfv.mm"
include "wceq.mm"
include "snssi.mm"
include "adantl.mm"
include "eqid.mm"
include "2polatN.mm"
include "wb.mm"
include "ispsubclN.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem atpsubclN
  let cA: class A
  let cC: class C
  let cQ: class Q
  let cK: class K
  assume 1psubcl.a: |- A = ( Atoms ` K )
  assume 1psubcl.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. HL /\ Q e. A ) -> { Q } e. C )

  proof
    cK
    chlt
    wcel
    #
    cQ
    cA
    wcel
    #
    wa
    cQ
    csn
    #
    cC
    wcel
    #
    @2
    cA
    wss
    #
    @2
    cK
    cpolN
    cfv
    #
    cfv
    @5
    cfv
    @2
    wceq
    #
    @1
    @4
    @0
    cQ
    cA
    snssi
    adantl
    cA
    @5
    cQ
    cK
    1psubcl.a
    @5
    eqid
    #
    2polatN
    @0
    @3
    @4
    @6
    wa
    wb
    @1
    cA
    cC
    chlt
    cK
    @5
    @2
    1psubcl.a
    @7
    1psubcl.c
    ispsubclN
    adantr
    mpbir2and
end
