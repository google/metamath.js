include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl1.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2.mm"
include "eqid.mm"
include "atbase.mm"
include "simpl3.mm"
include "simprl.mm"
include "simprr.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "latjass.mm"
include "syl13anc.mm"
include "hlatjass.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem 4atlem4a
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


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) ) -> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( P .\/ ( ( Q .\/ R ) .\/ S ) ) )

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
    #
    c.or
    co
    #
    cP
    cQ
    @8
    c.or
    co
    #
    c.or
    co
    #
    cP
    cQ
    cR
    c.or
    co
    cS
    c.or
    co
    #
    c.or
    co
    @7
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
    @14
    wcel
    #
    @8
    @14
    wcel
    #
    @9
    @11
    wceq
    @7
    @0
    @13
    @0
    @1
    @2
    @6
    simpl1
    #
    cK
    hllat
    syl
    @7
    @1
    @15
    @0
    @1
    @2
    @6
    simpl2
    cA
    @14
    cP
    cK
    @14
    eqid
    #
    4at.a
    atbase
    syl
    @7
    @2
    @16
    @0
    @1
    @2
    @6
    simpl3
    #
    cA
    @14
    cQ
    cK
    @19
    4at.a
    atbase
    syl
    @7
    @0
    @4
    @5
    @17
    @18
    @3
    @4
    @5
    simprl
    #
    @3
    @4
    @5
    simprr
    #
    cA
    @14
    c.or
    cK
    cR
    cS
    @19
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @14
    c.or
    cK
    cP
    cQ
    @8
    @19
    4at.j
    latjass
    syl13anc
    @7
    @12
    @10
    cP
    c.or
    @7
    @0
    @2
    @4
    @5
    @12
    @10
    wceq
    @18
    @20
    @21
    @22
    cA
    cQ
    cR
    cS
    c.or
    cK
    4at.j
    4at.a
    hlatjass
    syl13anc
    oveq2d
    eqtr4d
end
