include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "simpl.mm"
include "simprr.mm"
include "simprl.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "3impia.mm"

theorem 2llnne2N
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 2lnne.l: |- .<_ = ( le ` K )
  assume 2lnne.j: |- .\/ = ( join ` K )
  assume 2lnne.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ R e. A ) /\ -. P .<_ ( R .\/ Q ) ) -> ( R .\/ P ) =/= ( R .\/ Q ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    wa
    #
    cP
    cR
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    cR
    cP
    c.or
    co
    #
    @4
    wne
    @0
    @3
    wa
    #
    @5
    @6
    @4
    @7
    cP
    @6
    c.le
    wbr
    #
    @6
    @4
    wceq
    @5
    @7
    @0
    @2
    @1
    @8
    @0
    @3
    simpl
    @0
    @1
    @2
    simprr
    @0
    @1
    @2
    simprl
    cA
    cR
    cP
    c.or
    cK
    c.le
    2lnne.l
    2lnne.j
    2lnne.a
    hlatlej2
    syl3anc
    @6
    @4
    cP
    c.le
    breq2
    syl5ibcom
    necon3bd
    3impia
end
