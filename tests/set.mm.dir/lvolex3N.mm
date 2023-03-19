include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "cjn.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "eqid.mm"
include "islpln2.mm"
include "simp1l.mm"
include "simp1rl.mm"
include "simp1rr.mm"
include "simp2.mm"
include "3dim3.mm"
include "syl13anc.mm"
include "wb.mm"
include "simp33.mm"
include "breq2.mm"
include "notbid.mm"
include "rexbidv.mm"
include "syl.mm"
include "mpbird.mm"
include "rexlimdv3a.mm"
include "rexlimdvva.mm"
include "adantld.mm"
include "sylbid.mm"
include "imp.mm"

theorem lvolex3N
  let cA: class A
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  assume lvolex3.l: |- .<_ = ( le ` K )
  assume lvolex3.a: |- A = ( Atoms ` K )
  assume lvolex3.p: |- P = ( LPlanes ` K )

  disjoint A q
  disjoint K q
  disjoint .<_ q
  disjoint X q
  disjoint q r
  disjoint q s
  disjoint q t
  disjoint r s
  disjoint r t
  disjoint A r
  disjoint s t
  disjoint A s
  disjoint A t
  disjoint K r
  disjoint K s
  disjoint K t
  disjoint .<_ r
  disjoint .<_ s
  disjoint .<_ t
  disjoint X r
  disjoint X s
  disjoint X t
  assert |- ( ( K e. HL /\ X e. P ) -> E. q e. A -. q .<_ X )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
    wcel
    #
    vq
    cv
    #
    cX
    c.le
    wbr
    #
    wn
    #
    vq
    cA
    wrex
    #
    @0
    @1
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    vr
    cv
    #
    vs
    cv
    #
    wne
    #
    vt
    cv
    #
    @8
    @9
    cK
    cjn
    cfv
    #
    co
    #
    c.le
    wbr
    wn
    #
    cX
    @13
    @11
    @12
    co
    #
    wceq
    #
    w3a
    #
    vt
    cA
    wrex
    #
    vs
    cA
    wrex
    vr
    cA
    wrex
    #
    wa
    @5
    cA
    @6
    cP
    @12
    cK
    c.le
    cX
    vt
    vs
    vr
    @6
    eqid
    lvolex3.l
    @12
    eqid
    #
    lvolex3.a
    lvolex3.p
    islpln2
    @0
    @19
    @5
    @7
    @0
    @18
    @5
    vr
    vs
    cA
    cA
    @0
    @8
    cA
    wcel
    #
    @9
    cA
    wcel
    #
    wa
    #
    wa
    #
    @17
    @5
    vt
    cA
    @24
    @11
    cA
    wcel
    #
    @17
    w3a
    #
    @5
    @2
    @15
    c.le
    wbr
    #
    wn
    #
    vq
    cA
    wrex
    #
    @26
    @0
    @21
    @22
    @25
    @29
    @0
    @23
    @25
    @17
    simp1l
    @21
    @22
    @0
    @25
    @17
    simp1rl
    @21
    @22
    @0
    @25
    @17
    simp1rr
    @24
    @25
    @17
    simp2
    cA
    @8
    @9
    @11
    @12
    cK
    c.le
    vq
    @20
    lvolex3.l
    lvolex3.a
    3dim3
    syl13anc
    @26
    @16
    @5
    @29
    wb
    @24
    @25
    @10
    @14
    @16
    simp33
    @16
    @4
    @28
    vq
    cA
    @16
    @3
    @27
    cX
    @15
    @2
    c.le
    breq2
    notbid
    rexbidv
    syl
    mpbird
    rexlimdv3a
    rexlimdvva
    adantld
    sylbid
    imp
end
