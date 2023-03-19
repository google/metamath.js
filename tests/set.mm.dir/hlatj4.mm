include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp3r.mm"
include "latj4.mm"
include "syl122anc.mm"

theorem hlatj4
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  assume hlatjcom.j: |- .\/ = ( join ` K )
  assume hlatjcom.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) ) -> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( ( P .\/ R ) .\/ ( Q .\/ S ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    wa
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    wa
    #
    w3a
    #
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @9
    wcel
    #
    cR
    @9
    wcel
    #
    cS
    @9
    wcel
    #
    cP
    cQ
    c.or
    co
    cR
    cS
    c.or
    co
    c.or
    co
    cP
    cR
    c.or
    co
    cQ
    cS
    c.or
    co
    c.or
    co
    wceq
    @0
    @3
    @8
    @6
    cK
    hllat
    3ad2ant1
    @7
    @1
    @10
    @0
    @1
    @2
    @6
    simp2l
    cA
    @9
    cP
    cK
    @9
    eqid
    #
    hlatjcom.a
    atbase
    syl
    @7
    @2
    @11
    @0
    @1
    @2
    @6
    simp2r
    cA
    @9
    cQ
    cK
    @14
    hlatjcom.a
    atbase
    syl
    @7
    @4
    @12
    @0
    @3
    @4
    @5
    simp3l
    cA
    @9
    cR
    cK
    @14
    hlatjcom.a
    atbase
    syl
    @7
    @5
    @13
    @0
    @3
    @4
    @5
    simp3r
    cA
    @9
    cS
    cK
    @14
    hlatjcom.a
    atbase
    syl
    @9
    c.or
    cK
    cS
    cP
    cQ
    cR
    @14
    hlatjcom.j
    latj4
    syl122anc
end
