include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "crab.mm"
include "cbs.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simpl3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "pmapval.mm"
include "syl2anc.mm"
include "islinei.mm"
include "mpanr2.mm"
include "eqeltrd.mm"

theorem linepmap
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let cM: class M
  let cN: class N
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let cX: class X
  assume isline2.j: |- .\/ = ( join ` K )
  assume isline2.a: |- A = ( Atoms ` K )
  assume isline2.n: |- N = ( Lines ` K )
  assume isline2.m: |- M = ( pmap ` K )


  assert |- ( ( ( K e. Lat /\ P e. A /\ Q e. A ) /\ P =/= Q ) -> ( M ` ( P .\/ Q ) ) e. N )

  proof
    cK
    clat
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
    cP
    cQ
    wne
    #
    wa
    #
    cP
    cQ
    c.or
    co
    #
    cM
    cfv
    #
    vr
    cv
    @6
    cK
    cple
    cfv
    #
    wbr
    vr
    cA
    crab
    #
    cN
    @5
    @0
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @9
    wceq
    @0
    @1
    @2
    @4
    simpl1
    #
    @5
    @0
    cP
    @10
    wcel
    #
    cQ
    @10
    wcel
    #
    @11
    @12
    @5
    @1
    @13
    @0
    @1
    @2
    @4
    simpl2
    cA
    @10
    cP
    cK
    @10
    eqid
    #
    isline2.a
    atbase
    syl
    @5
    @2
    @14
    @0
    @1
    @2
    @4
    simpl3
    cA
    @10
    cQ
    cK
    @15
    isline2.a
    atbase
    syl
    @10
    c.or
    cK
    cP
    cQ
    @15
    isline2.j
    latjcl
    syl3anc
    cA
    @10
    clat
    cK
    @8
    cM
    @6
    vr
    @15
    @8
    eqid
    #
    isline2.a
    isline2.m
    pmapval
    syl2anc
    @3
    @4
    @9
    @9
    wceq
    @9
    cN
    wcel
    @9
    eqid
    cA
    clat
    cP
    cQ
    c.or
    cK
    @8
    cN
    @9
    vr
    @16
    isline2.j
    isline2.a
    isline2.n
    islinei
    mpanr2
    eqeltrd
end
