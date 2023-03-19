include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "adantr.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "atbase.mm"
include "syl.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "latref.mm"
include "syl2anc.mm"
include "wn.mm"
include "lvolnle3at.mm"
include "an32s.mm"
include "ex.mm"
include "mt2d.mm"

theorem 3atnelvolN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let cV: class V
  assume 3atnelvol.j: |- .\/ = ( join ` K )
  assume 3atnelvol.a: |- A = ( Atoms ` K )
  assume 3atnelvol.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> -. ( ( P .\/ Q ) .\/ R ) e. V )

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
    cR
    cA
    wcel
    #
    w3a
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
    cV
    wcel
    #
    @7
    @7
    cK
    cple
    cfv
    #
    wbr
    #
    @5
    cK
    clat
    wcel
    #
    @7
    cK
    cbs
    cfv
    #
    wcel
    #
    @10
    @0
    @11
    @4
    cK
    hllat
    adantr
    #
    @5
    @11
    @6
    @12
    wcel
    #
    cR
    @12
    wcel
    #
    @13
    @14
    @0
    @1
    @2
    @15
    @3
    cA
    @12
    c.or
    cK
    cP
    cQ
    @12
    eqid
    #
    3atnelvol.j
    3atnelvol.a
    hlatjcl
    3adant3r3
    @5
    @3
    @16
    @0
    @1
    @2
    @3
    simpr3
    cA
    @12
    cR
    cK
    @17
    3atnelvol.a
    atbase
    syl
    @12
    c.or
    cK
    @6
    cR
    @17
    3atnelvol.j
    latjcl
    syl3anc
    @12
    cK
    @9
    @7
    @17
    @9
    eqid
    #
    latref
    syl2anc
    @5
    @8
    @10
    wn
    #
    @0
    @8
    @4
    @19
    cA
    cP
    cQ
    cR
    c.or
    cK
    @9
    cV
    @7
    @18
    3atnelvol.j
    3atnelvol.a
    3atnelvol.v
    lvolnle3at
    an32s
    ex
    mt2d
end
