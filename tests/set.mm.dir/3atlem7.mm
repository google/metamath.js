include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpr.mm"
include "simpl3.mm"
include "3atlem6.mm"
include "syl131anc.mm"
include "3atlem5.mm"
include "pm2.61dan.mm"

theorem 3atlem7
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 3at.l: |- .<_ = ( le ` K )
  assume 3at.j: |- .\/ = ( join ` K )
  assume 3at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( -. R .<_ ( P .\/ Q ) /\ P =/= Q ) /\ ( ( P .\/ Q ) .\/ R ) .<_ ( ( S .\/ T ) .\/ U ) ) -> ( ( P .\/ Q ) .\/ R ) = ( ( S .\/ T ) .\/ U ) )

  proof
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cR
    cA
    wcel
    w3a
    cS
    cA
    wcel
    cT
    cA
    wcel
    cU
    cA
    wcel
    w3a
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
    cP
    cQ
    wne
    #
    wa
    #
    @1
    cR
    c.or
    co
    #
    cS
    cT
    c.or
    co
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    cQ
    cP
    cU
    c.or
    co
    c.le
    wbr
    #
    @5
    @6
    wceq
    #
    @8
    @9
    wa
    @0
    @2
    @3
    @9
    @7
    @10
    @0
    @4
    @7
    @9
    simpl1
    @2
    @3
    @0
    @7
    @9
    simpl2l
    @2
    @3
    @0
    @7
    @9
    simpl2r
    @8
    @9
    simpr
    @0
    @4
    @7
    @9
    simpl3
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    3atlem6
    syl131anc
    @8
    @9
    wn
    #
    wa
    @0
    @2
    @3
    @11
    @7
    @10
    @0
    @4
    @7
    @11
    simpl1
    @2
    @3
    @0
    @7
    @11
    simpl2l
    @2
    @3
    @0
    @7
    @11
    simpl2r
    @8
    @11
    simpr
    @0
    @4
    @7
    @11
    simpl3
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    3atlem5
    syl131anc
    pm2.61dan
end
