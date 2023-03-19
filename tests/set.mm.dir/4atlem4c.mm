include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "clat.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl1.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "adantr.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "latj12.mm"
include "syl13anc.mm"

theorem 4atlem4c
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


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) ) -> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( R .\/ ( ( P .\/ Q ) .\/ S ) ) )

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
    cK
    clat
    wcel
    #
    cP
    cQ
    c.or
    co
    #
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @10
    wcel
    #
    cS
    @10
    wcel
    #
    @9
    cR
    cS
    c.or
    co
    c.or
    co
    cR
    @9
    cS
    c.or
    co
    c.or
    co
    wceq
    @7
    @0
    @8
    @0
    @1
    @2
    @6
    simpl1
    cK
    hllat
    syl
    @3
    @11
    @6
    cA
    @10
    c.or
    cK
    cP
    cQ
    @10
    eqid
    #
    4at.j
    4at.a
    hlatjcl
    adantr
    @4
    @12
    @3
    @5
    cA
    @10
    cR
    cK
    @14
    4at.a
    atbase
    ad2antrl
    @5
    @13
    @3
    @4
    cA
    @10
    cS
    cK
    @14
    4at.a
    atbase
    ad2antll
    @10
    c.or
    cK
    @9
    cR
    cS
    @14
    4at.j
    latj12
    syl13anc
end
