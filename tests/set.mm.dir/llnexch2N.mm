include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "llnexchb2.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "eqid.mm"
include "llnbase.mm"
include "syl.mm"
include "simp22.mm"
include "latmle2.mm"
include "syl3anc.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "sylbid.mm"

theorem llnexch2N
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  assume llnexch.l: |- .<_ = ( le ` K )
  assume llnexch.j: |- .\/ = ( join ` K )
  assume llnexch.m: |- ./\ = ( meet ` K )
  assume llnexch.a: |- A = ( Atoms ` K )
  assume llnexch.n: |- N = ( LLines ` K )


  assert |- ( ( K e. HL /\ ( X e. N /\ Y e. N /\ Z e. N ) /\ ( ( X ./\ Y ) e. A /\ X =/= Z ) ) -> ( ( X ./\ Y ) .<_ Z -> ( X ./\ Z ) .<_ Y ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cY
    cN
    wcel
    #
    cZ
    cN
    wcel
    #
    w3a
    #
    cX
    cY
    c.an
    co
    #
    cA
    wcel
    cX
    cZ
    wne
    wa
    #
    w3a
    #
    @5
    cZ
    c.le
    wbr
    @5
    cX
    cZ
    c.an
    co
    #
    wceq
    #
    @8
    cY
    c.le
    wbr
    #
    cA
    c.or
    cK
    c.le
    c.an
    cN
    cX
    cY
    cZ
    llnexch.l
    llnexch.j
    llnexch.m
    llnexch.a
    llnexch.n
    llnexchb2
    @7
    @5
    cY
    c.le
    wbr
    #
    @9
    @10
    @7
    cK
    clat
    wcel
    #
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    cY
    @13
    wcel
    #
    @11
    @0
    @4
    @12
    @6
    cK
    hllat
    3ad2ant1
    @7
    @1
    @14
    @0
    @1
    @2
    @3
    @6
    simp21
    @13
    cK
    cN
    cX
    @13
    eqid
    #
    llnexch.n
    llnbase
    syl
    @7
    @2
    @15
    @0
    @1
    @2
    @3
    @6
    simp22
    @13
    cK
    cN
    cY
    @16
    llnexch.n
    llnbase
    syl
    @13
    cK
    c.le
    c.an
    cX
    cY
    @16
    llnexch.l
    llnexch.m
    latmle2
    syl3anc
    @5
    @8
    cY
    c.le
    breq1
    syl5ibcom
    sylbid
end
