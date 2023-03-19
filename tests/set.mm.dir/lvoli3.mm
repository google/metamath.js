include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "eqidd.mm"
include "breq2.mm"
include "notbid.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "breq1.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simpl1.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "lplnbase.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "islvol3.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem lvoli3
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let vr: setvar r
  let vy: setvar y
  assume lvoli3.l: |- .<_ = ( le ` K )
  assume lvoli3.j: |- .\/ = ( join ` K )
  assume lvoli3.a: |- A = ( Atoms ` K )
  assume lvoli3.p: |- P = ( LPlanes ` K )
  assume lvoli3.v: |- V = ( LVols ` K )


  assert |- ( ( ( K e. HL /\ X e. P /\ Q e. A ) /\ -. Q .<_ X ) -> ( X .\/ Q ) e. V )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cQ
    cX
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cX
    cQ
    c.or
    co
    #
    cV
    wcel
    #
    vr
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    wn
    #
    @7
    @10
    @9
    c.or
    co
    #
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    vy
    cP
    wrex
    #
    @6
    @1
    @2
    @5
    @7
    @7
    wceq
    #
    @16
    @0
    @1
    @2
    @5
    simpl2
    #
    @0
    @1
    @2
    @5
    simpl3
    #
    @3
    @5
    simpr
    @6
    @7
    eqidd
    @15
    @5
    @17
    wa
    @9
    cX
    c.le
    wbr
    #
    wn
    #
    @7
    cX
    @9
    c.or
    co
    #
    wceq
    #
    wa
    vy
    vr
    cX
    cQ
    cP
    cA
    @10
    cX
    wceq
    #
    @12
    @21
    @14
    @23
    @24
    @11
    @20
    @10
    cX
    @9
    c.le
    breq2
    notbid
    @24
    @13
    @22
    @7
    @10
    cX
    @9
    c.or
    oveq1
    eqeq2d
    anbi12d
    @9
    cQ
    wceq
    #
    @21
    @5
    @23
    @17
    @25
    @20
    @4
    @9
    cQ
    cX
    c.le
    breq1
    notbid
    @25
    @22
    @7
    @7
    @9
    cQ
    cX
    c.or
    oveq2
    eqeq2d
    anbi12d
    rspc2ev
    syl112anc
    @6
    @0
    @7
    cK
    cbs
    cfv
    #
    wcel
    #
    @8
    @16
    wb
    @0
    @1
    @2
    @5
    simpl1
    #
    @6
    cK
    clat
    wcel
    #
    cX
    @26
    wcel
    #
    cQ
    @26
    wcel
    #
    @27
    @6
    @0
    @29
    @28
    cK
    hllat
    syl
    @6
    @1
    @30
    @18
    @26
    cP
    cK
    cX
    @26
    eqid
    #
    lvoli3.p
    lplnbase
    syl
    @6
    @2
    @31
    @19
    cA
    @26
    cQ
    cK
    @32
    lvoli3.a
    atbase
    syl
    @26
    c.or
    cK
    cX
    cQ
    @32
    lvoli3.j
    latjcl
    syl3anc
    vy
    cA
    @26
    cP
    c.or
    cK
    c.le
    cV
    @7
    vr
    @32
    lvoli3.l
    lvoli3.j
    lvoli3.a
    lvoli3.p
    lvoli3.v
    islvol3
    syl2anc
    mpbird
end
