include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpr.mm"
include "jca.mm"
include "simpl23.mm"
include "simpl3.mm"
include "3atlem2.mm"
include "syl131anc.mm"
include "3atlem1.mm"
include "pm2.61dan.mm"

theorem 3atlem3
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


  assert |- ( ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( -. R .<_ ( P .\/ Q ) /\ P =/= U /\ -. Q .<_ ( P .\/ U ) ) /\ ( ( P .\/ Q ) .\/ R ) .<_ ( ( S .\/ T ) .\/ U ) ) -> ( ( P .\/ Q ) .\/ R ) = ( ( S .\/ T ) .\/ U ) )

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
    cU
    wne
    #
    cQ
    cP
    cU
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
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
    cP
    cT
    cU
    c.or
    co
    c.le
    wbr
    #
    @6
    @7
    wceq
    #
    @9
    @10
    wa
    #
    @0
    @2
    @3
    @10
    wa
    @4
    @8
    @11
    @0
    @5
    @8
    @10
    simpl1
    @2
    @3
    @4
    @0
    @8
    @10
    simpl21
    @12
    @3
    @10
    @2
    @3
    @4
    @0
    @8
    @10
    simpl22
    @9
    @10
    simpr
    jca
    @2
    @3
    @4
    @0
    @8
    @10
    simpl23
    @0
    @5
    @8
    @10
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
    3atlem2
    syl131anc
    @9
    @10
    wn
    #
    wa
    @0
    @2
    @13
    @4
    @8
    @11
    @0
    @5
    @8
    @13
    simpl1
    @2
    @3
    @4
    @0
    @8
    @13
    simpl21
    @9
    @13
    simpr
    @2
    @3
    @4
    @0
    @8
    @13
    simpl23
    @0
    @5
    @8
    @13
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
    3atlem1
    syl131anc
    pm2.61dan
end
