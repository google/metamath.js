include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "cjn.mm"
include "co.mm"
include "wa.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "catm.mm"
include "cal.mm"
include "clc.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "notbid.mm"
include "eqidd.mm"
include "oveqd.mm"
include "breq123d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "df-cvlat.mm"
include "elrab2.mm"

theorem iscvlat
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  assume iscvlat.b: |- B = ( Base ` K )
  assume iscvlat.l: |- .<_ = ( le ` K )
  assume iscvlat.j: |- .\/ = ( join ` K )
  assume iscvlat.a: |- A = ( Atoms ` K )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint B x
  disjoint p x
  disjoint K p
  disjoint q x
  disjoint K q
  disjoint K x
  disjoint k p
  disjoint k q
  disjoint A k
  disjoint k x
  disjoint B k
  disjoint .<_ k
  disjoint .\/ k
  disjoint K k
  assert |- ( K e. CvLat <-> ( K e. AtLat /\ A. p e. A A. q e. A A. x e. B ( ( -. p .<_ x /\ p .<_ ( x .\/ q ) ) -> q .<_ ( x .\/ p ) ) ) )

  proof
    vp
    cv
    #
    vx
    cv
    #
    vk
    cv
    #
    cple
    cfv
    #
    wbr
    #
    wn
    #
    @0
    @1
    vq
    cv
    #
    @2
    cjn
    cfv
    #
    co
    #
    @3
    wbr
    #
    wa
    #
    @6
    @1
    @0
    @7
    co
    #
    @3
    wbr
    #
    wi
    #
    vx
    @2
    cbs
    cfv
    #
    wral
    #
    vq
    @2
    catm
    cfv
    #
    wral
    #
    vp
    @16
    wral
    @0
    @1
    c.le
    wbr
    #
    wn
    #
    @0
    @1
    @6
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    @6
    @1
    @0
    c.or
    co
    #
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
    #
    vp
    cA
    wral
    vk
    cK
    cal
    clc
    @2
    cK
    wceq
    #
    @17
    @27
    vp
    @16
    cA
    @28
    @16
    cK
    catm
    cfv
    cA
    @2
    cK
    catm
    fveq2
    iscvlat.a
    syl6eqr
    #
    @28
    @15
    @26
    vq
    @16
    cA
    @29
    @28
    @13
    @25
    vx
    @14
    cB
    @28
    @14
    cK
    cbs
    cfv
    cB
    @2
    cK
    cbs
    fveq2
    iscvlat.b
    syl6eqr
    @28
    @10
    @22
    @12
    @24
    @28
    @5
    @19
    @9
    @21
    @28
    @4
    @18
    @28
    @3
    c.le
    @0
    @1
    @28
    @3
    cK
    cple
    cfv
    c.le
    @2
    cK
    cple
    fveq2
    iscvlat.l
    syl6eqr
    #
    breqd
    notbid
    @28
    @0
    @0
    @8
    @20
    @3
    c.le
    @28
    @0
    eqidd
    @30
    @28
    @7
    c.or
    @1
    @6
    @28
    @7
    cK
    cjn
    cfv
    c.or
    @2
    cK
    cjn
    fveq2
    iscvlat.j
    syl6eqr
    #
    oveqd
    breq123d
    anbi12d
    @28
    @6
    @6
    @11
    @23
    @3
    c.le
    @28
    @6
    eqidd
    @30
    @28
    @7
    c.or
    @1
    @0
    @31
    oveqd
    breq123d
    imbi12d
    raleqbidv
    raleqbidv
    raleqbidv
    vk
    vp
    vq
    vx
    df-cvlat
    elrab2
end
