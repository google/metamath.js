include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simprr.mm"
include "cbs.mm"
include "cfv.mm"
include "wi.mm"
include "simpl1.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simprl.mm"
include "hlexch1.mm"
include "syl131anc.mm"
include "mtod.mm"

theorem 4atlem0a
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


  assert |- ( ( ( K e. HL /\ ( P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) ) /\ ( -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> -. R .<_ ( ( P .\/ Q ) .\/ S ) )

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
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cS
    @8
    cR
    c.or
    co
    c.le
    wbr
    #
    wn
    #
    wa
    #
    wa
    #
    cR
    @8
    cS
    c.or
    co
    c.le
    wbr
    #
    @10
    @7
    @9
    @11
    simprr
    @13
    @0
    @4
    @5
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    @9
    @14
    @10
    wi
    @0
    @3
    @6
    @12
    simpl1
    #
    @4
    @5
    @0
    @3
    @12
    simpl3l
    @4
    @5
    @0
    @3
    @12
    simpl3r
    @13
    @0
    @1
    @2
    @16
    @17
    @1
    @2
    @0
    @6
    @12
    simpl2l
    @1
    @2
    @0
    @6
    @12
    simpl2r
    cA
    @15
    c.or
    cK
    cP
    cQ
    @15
    eqid
    #
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @7
    @9
    @11
    simprl
    cA
    @15
    cR
    cS
    c.or
    cK
    c.le
    @8
    @18
    4at.l
    4at.j
    4at.a
    hlexch1
    syl131anc
    mtod
end
