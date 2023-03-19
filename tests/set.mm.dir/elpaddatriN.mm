include "clat.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "csn.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "snssd.mm"
include "simpr1.mm"
include "snidg.mm"
include "syl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "elpaddri.mm"
include "syl322anc.mm"

theorem elpaddatriN
  let cA: class A
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vs: setvar s
  let vq: setvar q
  let vr: setvar r
  let cY: class Y
  assume paddfval.l: |- .<_ = ( le ` K )
  assume paddfval.j: |- .\/ = ( join ` K )
  assume paddfval.a: |- A = ( Atoms ` K )
  assume paddfval.p: |- .+ = ( +P ` K )


  assert |- ( ( ( K e. Lat /\ X C_ A /\ Q e. A ) /\ ( R e. X /\ S e. A /\ S .<_ ( R .\/ Q ) ) ) -> S e. ( X .+ { Q } ) )

  proof
    cK
    clat
    wcel
    #
    cX
    cA
    wss
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cR
    cX
    wcel
    #
    cS
    cA
    wcel
    #
    cS
    cR
    cQ
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    @0
    @1
    cQ
    csn
    #
    cA
    wss
    @4
    cQ
    @9
    wcel
    #
    @5
    @6
    cS
    cX
    @9
    c.pl
    co
    wcel
    @0
    @1
    @2
    @7
    simpl1
    @0
    @1
    @2
    @7
    simpl2
    @8
    cQ
    cA
    @0
    @1
    @2
    @7
    simpl3
    #
    snssd
    @3
    @4
    @5
    @6
    simpr1
    @8
    @2
    @10
    @11
    cQ
    cA
    snidg
    syl
    @3
    @4
    @5
    @6
    simpr2
    @3
    @4
    @5
    @6
    simpr3
    cA
    c.pl
    cR
    cQ
    cS
    c.or
    cK
    c.le
    cX
    @9
    paddfval.l
    paddfval.j
    paddfval.a
    paddfval.p
    elpaddri
    syl322anc
end
