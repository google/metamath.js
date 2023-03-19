include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simprl.mm"
include "simprr.mm"
include "hlatj4.mm"
include "syl122anc.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "atbase.mm"
include "ad2antll.mm"
include "latj12.mm"
include "syl13anc.mm"
include "eqtrd.mm"

theorem 4atlem4b
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) ) -> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( Q .\/ ( ( P .\/ R ) .\/ S ) ) )

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
    w3a
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
    wa
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
    #
    cP
    cR
    c.or
    co
    #
    cQ
    cS
    c.or
    co
    c.or
    co
    #
    cQ
    @9
    cS
    c.or
    co
    c.or
    co
    #
    @7
    @0
    @1
    @2
    @4
    @5
    @8
    @10
    wceq
    @0
    @1
    @2
    @6
    simpl1
    #
    @0
    @1
    @2
    @6
    simpl2
    #
    @0
    @1
    @2
    @6
    simpl3
    #
    @3
    @4
    @5
    simprl
    #
    @3
    @4
    @5
    simprr
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    4at.j
    4at.a
    hlatj4
    syl122anc
    @7
    cK
    clat
    wcel
    #
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @17
    wcel
    #
    cS
    @17
    wcel
    #
    @10
    @11
    wceq
    @7
    @0
    @16
    @12
    cK
    hllat
    syl
    @7
    @0
    @1
    @4
    @18
    @12
    @13
    @15
    cA
    @17
    c.or
    cK
    cP
    cR
    @17
    eqid
    #
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @7
    @2
    @19
    @14
    cA
    @17
    cQ
    cK
    @21
    4at.a
    atbase
    syl
    @5
    @20
    @3
    @4
    cA
    @17
    cS
    cK
    @21
    4at.a
    atbase
    ad2antll
    @17
    c.or
    cK
    @9
    cQ
    cS
    @21
    4at.j
    latj12
    syl13anc
    eqtrd
end
