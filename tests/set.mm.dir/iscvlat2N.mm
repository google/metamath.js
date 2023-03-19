include "clc.mm"
include "wcel.mm"
include "cal.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "iscvlat.mm"
include "wb.mm"
include "simpll.mm"
include "simplrl.mm"
include "simpr.mm"
include "atnle.mm"
include "syl3anc.mm"
include "anbi1d.mm"
include "imbi1d.mm"
include "ralbidva.mm"
include "2ralbidva.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem iscvlat2N
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.0: class .0.
  let vq: setvar q
  let vp: setvar p
  assume iscvlat2.b: |- B = ( Base ` K )
  assume iscvlat2.l: |- .<_ = ( le ` K )
  assume iscvlat2.j: |- .\/ = ( join ` K )
  assume iscvlat2.m: |- ./\ = ( meet ` K )
  assume iscvlat2.z: |- .0. = ( 0. ` K )
  assume iscvlat2.a: |- A = ( Atoms ` K )

  disjoint p q
  disjoint p x
  disjoint A p
  disjoint q x
  disjoint A q
  disjoint A x
  disjoint B x
  disjoint K p
  disjoint K q
  disjoint K x
  assert |- ( K e. CvLat <-> ( K e. AtLat /\ A. p e. A A. q e. A A. x e. B ( ( ( p ./\ x ) = .0. /\ p .<_ ( x .\/ q ) ) -> q .<_ ( x .\/ p ) ) ) )

  proof
    cK
    clc
    wcel
    cK
    cal
    wcel
    #
    vp
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    wn
    #
    @1
    @2
    vq
    cv
    #
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    @4
    @2
    @1
    c.or
    co
    c.le
    wbr
    #
    wi
    #
    vx
    cB
    wral
    #
    vq
    cA
    wral
    vp
    cA
    wral
    #
    wa
    @0
    @1
    @2
    c.an
    co
    c.0
    wceq
    #
    @5
    wa
    #
    @7
    wi
    #
    vx
    cB
    wral
    #
    vq
    cA
    wral
    vp
    cA
    wral
    #
    wa
    vx
    cA
    cB
    c.or
    cK
    c.le
    vq
    vp
    iscvlat2.b
    iscvlat2.l
    iscvlat2.j
    iscvlat2.a
    iscvlat
    @0
    @10
    @15
    @0
    @9
    @14
    vp
    vq
    cA
    cA
    @0
    @1
    cA
    wcel
    #
    @4
    cA
    wcel
    #
    wa
    #
    wa
    #
    @8
    @13
    vx
    cB
    @19
    @2
    cB
    wcel
    #
    wa
    #
    @6
    @12
    @7
    @21
    @3
    @11
    @5
    @21
    @0
    @16
    @20
    @3
    @11
    wb
    @0
    @18
    @20
    simpll
    @0
    @16
    @17
    @20
    simplrl
    @19
    @20
    simpr
    cA
    cB
    @1
    cK
    c.le
    c.an
    @2
    c.0
    iscvlat2.b
    iscvlat2.l
    iscvlat2.m
    iscvlat2.z
    iscvlat2.a
    atnle
    syl3anc
    anbi1d
    imbi1d
    ralbidva
    2ralbidva
    pm5.32i
    bitri
end
