include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp2l.mm"
include "simp3.mm"
include "eqid.mm"
include "cdlemg2k.mm"
include "syl121anc.mm"
include "simp1l.mm"
include "simp2ll.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp2rl.mm"
include "hlatjcom.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem cdlemg2kq
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cX: class X
  assume cdlemg2inv.h: |- H = ( LHyp ` K )
  assume cdlemg2inv.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg2j.l: |- .<_ = ( le ` K )
  assume cdlemg2j.j: |- .\/ = ( join ` K )
  assume cdlemg2j.a: |- A = ( Atoms ` K )
  assume cdlemg2j.m: |- ./\ = ( meet ` K )
  assume cdlemg2j.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ F e. T ) -> ( ( F ` P ) .\/ ( F ` Q ) ) = ( ( F ` Q ) .\/ U ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cF
    cT
    wcel
    #
    w3a
    #
    cQ
    cF
    cfv
    #
    cP
    cF
    cfv
    #
    c.or
    co
    #
    @12
    cQ
    cP
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    @13
    @12
    c.or
    co
    #
    @12
    cU
    c.or
    co
    @11
    @2
    @8
    @5
    @10
    @14
    @17
    wceq
    @2
    @9
    @10
    simp1
    #
    @2
    @5
    @8
    @10
    simp2r
    @2
    @5
    @8
    @10
    simp2l
    @2
    @9
    @10
    simp3
    #
    cA
    cQ
    cP
    cT
    @16
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg2inv.h
    cdlemg2inv.t
    cdlemg2j.l
    cdlemg2j.j
    cdlemg2j.a
    cdlemg2j.m
    @16
    eqid
    cdlemg2k
    syl121anc
    @11
    @0
    @13
    cA
    wcel
    #
    @12
    cA
    wcel
    #
    @18
    @14
    wceq
    @0
    @1
    @9
    @10
    simp1l
    #
    @11
    @2
    @10
    @3
    @21
    @19
    @20
    @3
    @4
    @8
    @2
    @10
    simp2ll
    #
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg2j.l
    cdlemg2j.a
    cdlemg2inv.h
    cdlemg2inv.t
    ltrnat
    syl3anc
    @11
    @2
    @10
    @6
    @22
    @19
    @20
    @6
    @7
    @5
    @2
    @10
    simp2rl
    #
    cA
    cQ
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg2j.l
    cdlemg2j.a
    cdlemg2inv.h
    cdlemg2inv.t
    ltrnat
    syl3anc
    cA
    c.or
    cK
    @13
    @12
    cdlemg2j.j
    cdlemg2j.a
    hlatjcom
    syl3anc
    @11
    cU
    @16
    @12
    c.or
    @11
    cU
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    @16
    cdlemg2j.u
    @11
    @26
    @15
    cW
    c.an
    @11
    @0
    @3
    @6
    @26
    @15
    wceq
    @23
    @24
    @25
    cA
    c.or
    cK
    cP
    cQ
    cdlemg2j.j
    cdlemg2j.a
    hlatjcom
    syl3anc
    oveq1d
    syl5eq
    oveq2d
    3eqtr4d
end
