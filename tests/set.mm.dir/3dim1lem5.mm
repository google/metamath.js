include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "weq.mm"
include "neeq2.mm"
include "oveq2.mm"
include "breq2d.mm"
include "notbid.mm"
include "oveq1d.mm"
include "3anbi123d.mm"
include "breq1.mm"
include "3anbi23d.mm"
include "3anbi3d.mm"
include "rspc3ev.mm"

theorem 3dim1lem5
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vt: setvar t
  assume 3dim0.j: |- .\/ = ( join ` K )
  assume 3dim0.l: |- .<_ = ( le ` K )
  assume 3dim0.a: |- A = ( Atoms ` K )

  disjoint q r
  disjoint q s
  disjoint A q
  disjoint r s
  disjoint A r
  disjoint A s
  disjoint .\/ r
  disjoint .\/ s
  disjoint u v
  disjoint u w
  disjoint A u
  disjoint v w
  disjoint A v
  disjoint A w
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint .\/ q
  disjoint .\/ u
  disjoint .\/ v
  disjoint .\/ w
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint .<_ q
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint .<_ r
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint .<_ s
  disjoint .<_ u
  disjoint .<_ v
  disjoint .<_ w
  disjoint P q
  disjoint P r
  disjoint P s
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint A p
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint A t
  disjoint q t
  disjoint .\/ t
  disjoint K t
  disjoint r t
  disjoint s t
  disjoint .<_ t
  disjoint P t
  assert |- ( ( ( u e. A /\ v e. A /\ w e. A ) /\ ( P =/= u /\ -. v .<_ ( P .\/ u ) /\ -. w .<_ ( ( P .\/ u ) .\/ v ) ) ) -> E. q e. A E. r e. A E. s e. A ( P =/= q /\ -. r .<_ ( P .\/ q ) /\ -. s .<_ ( ( P .\/ q ) .\/ r ) ) )

  proof
    cP
    vq
    cv
    #
    wne
    #
    vr
    cv
    #
    cP
    @0
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    vs
    cv
    #
    @3
    @2
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    cP
    vu
    cv
    #
    wne
    #
    vv
    cv
    #
    cP
    @10
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    vw
    cv
    #
    @13
    @12
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    @11
    @2
    @13
    c.le
    wbr
    #
    wn
    #
    @6
    @13
    @2
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    @11
    @15
    @6
    @17
    c.le
    wbr
    #
    wn
    #
    w3a
    vq
    vr
    vs
    @10
    @12
    @16
    cA
    cA
    cA
    vq
    vu
    weq
    #
    @1
    @11
    @5
    @21
    @9
    @24
    @0
    @10
    cP
    neeq2
    @27
    @4
    @20
    @27
    @3
    @13
    @2
    c.le
    @0
    @10
    cP
    c.or
    oveq2
    #
    breq2d
    notbid
    @27
    @8
    @23
    @27
    @7
    @22
    @6
    c.le
    @27
    @3
    @13
    @2
    c.or
    @28
    oveq1d
    breq2d
    notbid
    3anbi123d
    vr
    vv
    weq
    #
    @21
    @15
    @24
    @26
    @11
    @29
    @20
    @14
    @2
    @12
    @13
    c.le
    breq1
    notbid
    @29
    @23
    @25
    @29
    @22
    @17
    @6
    c.le
    @2
    @12
    @13
    c.or
    oveq2
    breq2d
    notbid
    3anbi23d
    vs
    vw
    weq
    #
    @26
    @19
    @11
    @15
    @30
    @25
    @18
    @6
    @16
    @17
    c.le
    breq1
    notbid
    3anbi3d
    rspc3ev
end
