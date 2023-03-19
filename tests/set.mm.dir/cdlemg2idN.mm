include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "cv.mm"
include "cmee.mm"
include "co.mm"
include "cjn.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "csb.mm"
include "cif.mm"
include "cmpt.mm"
include "simp111.mm"
include "simp112.mm"
include "simp12.mm"
include "simp13.mm"
include "simp113.mm"
include "simp2l.mm"
include "eqid.mm"
include "cdlemg2dN.mm"
include "syl222anc.mm"
include "fveq1d.mm"
include "simp2r.mm"
include "simp3.mm"
include "cdleme31id.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem cdlemg2idN
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cdlemg2id.l: |- .<_ = ( le ` K )
  assume cdlemg2id.a: |- A = ( Atoms ` K )
  assume cdlemg2id.h: |- H = ( LHyp ` K )
  assume cdlemg2id.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg2id.b: |- B = ( Base ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H /\ F e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( F ` P ) = Q /\ X e. B ) /\ P = Q ) -> ( F ` X ) = X )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    cF
    cT
    wcel
    #
    w3a
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
    w3a
    #
    cP
    cF
    cfv
    cQ
    wceq
    #
    cX
    cB
    wcel
    #
    wa
    #
    cP
    cQ
    wceq
    #
    w3a
    #
    cX
    cF
    cfv
    cX
    vx
    cB
    cP
    cQ
    wne
    vx
    cv
    #
    cW
    c.le
    wbr
    wn
    wa
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    @13
    @12
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cjn
    cfv
    #
    co
    @12
    wceq
    wa
    vz
    cv
    @13
    cP
    cQ
    @16
    co
    #
    c.le
    wbr
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @18
    @17
    c.le
    wbr
    wn
    wa
    vy
    cv
    @17
    @18
    @17
    cW
    @14
    co
    #
    @16
    co
    cQ
    cP
    @18
    @16
    co
    cW
    @14
    co
    @16
    co
    @14
    co
    #
    @13
    @18
    @16
    co
    cW
    @14
    co
    @16
    co
    @14
    co
    #
    wceq
    wi
    vt
    cA
    wral
    vy
    cB
    crio
    vt
    @13
    @20
    csb
    cif
    @15
    @16
    co
    wceq
    wi
    vs
    cA
    wral
    vz
    cB
    crio
    #
    @12
    cif
    cmpt
    #
    cfv
    #
    cX
    @11
    cX
    cF
    @23
    @11
    @0
    @1
    @4
    @5
    @2
    @7
    cF
    @23
    wceq
    @0
    @1
    @2
    @4
    @5
    @9
    @10
    simp111
    @0
    @1
    @2
    @4
    @5
    @9
    @10
    simp112
    @3
    @4
    @5
    @9
    @10
    simp12
    @3
    @4
    @5
    @9
    @10
    simp13
    @0
    @1
    @2
    @4
    @5
    @9
    @10
    simp113
    @6
    @7
    @8
    @10
    simp2l
    vx
    vy
    vz
    vt
    cA
    cB
    @20
    cP
    cQ
    cT
    @19
    @21
    cF
    @23
    cH
    @16
    cK
    c.le
    @14
    cW
    vs
    cdlemg2id.b
    cdlemg2id.l
    @16
    eqid
    @14
    eqid
    cdlemg2id.a
    cdlemg2id.h
    cdlemg2id.t
    @19
    eqid
    @20
    eqid
    @21
    eqid
    @23
    eqid
    #
    cdlemg2dN
    syl222anc
    fveq1d
    @11
    @8
    @10
    @24
    cX
    wceq
    @6
    @7
    @8
    @10
    simp2r
    @6
    @9
    @10
    simp3
    vx
    cB
    cP
    cQ
    @23
    c.le
    @22
    cW
    cX
    @25
    cdleme31id
    syl2anc
    eqtrd
end
