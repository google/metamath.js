include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cdlemg2k.mm"
include "3adant3l.mm"
include "fveq2d.mm"
include "cbs.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp3r.mm"
include "simp2l.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simpld.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp2r.mm"
include "ltrnj.mm"
include "syl112anc.mm"
include "cdlemg2fv2.mm"
include "syl131anc.mm"
include "3eqtr3d.mm"

theorem cdlemg2l
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T ) ) -> ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) = ( ( F ` ( G ` P ) ) .\/ U ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    wa
    #
    w3a
    #
    cP
    cG
    cfv
    #
    cQ
    cG
    cfv
    #
    c.or
    co
    #
    cF
    cfv
    #
    @8
    cU
    c.or
    co
    #
    cF
    cfv
    #
    @8
    cF
    cfv
    #
    @9
    cF
    cfv
    c.or
    co
    #
    @14
    cU
    c.or
    co
    #
    @7
    @10
    @12
    cF
    @0
    @3
    @5
    @10
    @12
    wceq
    @4
    cA
    cP
    cQ
    cT
    cU
    cG
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
    cdlemg2j.u
    cdlemg2k
    3adant3l
    fveq2d
    @7
    @0
    @4
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    @9
    @17
    wcel
    #
    @11
    @15
    wceq
    @0
    @3
    @6
    simp1
    #
    @0
    @3
    @4
    @5
    simp3l
    #
    @7
    @8
    cA
    wcel
    #
    @18
    @7
    @22
    @8
    cW
    c.le
    wbr
    wn
    #
    @7
    @0
    @5
    @1
    @22
    @23
    wa
    #
    @20
    @0
    @3
    @4
    @5
    simp3r
    #
    @0
    @1
    @2
    @6
    simp2l
    #
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg2j.l
    cdlemg2j.a
    cdlemg2inv.h
    cdlemg2inv.t
    ltrnel
    syl3anc
    #
    simpld
    cA
    @17
    @8
    cK
    @17
    eqid
    #
    cdlemg2j.a
    atbase
    syl
    @7
    @9
    cA
    wcel
    #
    @19
    @7
    @29
    @9
    cW
    c.le
    wbr
    wn
    #
    @7
    @0
    @5
    @2
    @29
    @30
    wa
    @20
    @25
    @0
    @1
    @2
    @6
    simp2r
    #
    cA
    cQ
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg2j.l
    cdlemg2j.a
    cdlemg2inv.h
    cdlemg2inv.t
    ltrnel
    syl3anc
    simpld
    cA
    @17
    @9
    cK
    @28
    cdlemg2j.a
    atbase
    syl
    @17
    cT
    cF
    cH
    c.or
    cK
    cW
    @8
    @9
    @28
    cdlemg2j.j
    cdlemg2inv.h
    cdlemg2inv.t
    ltrnj
    syl112anc
    @7
    @0
    @1
    @2
    @24
    @4
    @13
    @16
    wceq
    @20
    @26
    @31
    @27
    @21
    cA
    cP
    cQ
    @8
    cT
    cU
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
    cdlemg2j.u
    cdlemg2fv2
    syl131anc
    3eqtr3d
end
