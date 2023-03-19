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
include "eqid.mm"
include "hlatjcl.mm"
include "adantr.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "latjass.mm"
include "syl13anc.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "latjcom.mm"
include "eqtr3d.mm"

theorem 4atlem4d
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


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) ) -> ( ( P .\/ Q ) .\/ ( R .\/ S ) ) = ( S .\/ ( ( P .\/ Q ) .\/ R ) ) )

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
    #
    cR
    c.or
    co
    #
    cS
    c.or
    co
    #
    @8
    cR
    cS
    c.or
    co
    c.or
    co
    #
    cS
    @9
    c.or
    co
    #
    @7
    cK
    clat
    wcel
    #
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @14
    wcel
    #
    cS
    @14
    wcel
    #
    @10
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
    cK
    hllat
    syl
    #
    @3
    @15
    @6
    cA
    @14
    c.or
    cK
    cP
    cQ
    @14
    eqid
    #
    4at.j
    4at.a
    hlatjcl
    adantr
    #
    @4
    @16
    @3
    @5
    cA
    @14
    cR
    cK
    @19
    4at.a
    atbase
    ad2antrl
    #
    @5
    @17
    @3
    @4
    cA
    @14
    cS
    cK
    @19
    4at.a
    atbase
    ad2antll
    #
    @14
    c.or
    cK
    @8
    cR
    cS
    @19
    4at.j
    latjass
    syl13anc
    @7
    @13
    @9
    @14
    wcel
    #
    @17
    @10
    @12
    wceq
    @18
    @7
    @13
    @15
    @16
    @23
    @18
    @20
    @21
    @14
    c.or
    cK
    @8
    cR
    @19
    4at.j
    latjcl
    syl3anc
    @22
    @14
    c.or
    cK
    @9
    cS
    @19
    4at.j
    latjcom
    syl3anc
    eqtr3d
end
