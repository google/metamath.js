include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "adantl.mm"
include "wne.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simpr.mm"
include "ctrl.mm"
include "eqid.mm"
include "cdlemg39.mm"
include "syl113anc.mm"
include "pm2.61dane.mm"

theorem cdlemg40
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg35.l: |- .<_ = ( le ` K )
  assume cdlemg35.j: |- .\/ = ( join ` K )
  assume cdlemg35.m: |- ./\ = ( meet ` K )
  assume cdlemg35.a: |- A = ( Atoms ` K )
  assume cdlemg35.h: |- H = ( LHyp ` K )
  assume cdlemg35.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
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
    cP
    cG
    cfv
    #
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    cQ
    cQ
    cG
    cfv
    #
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    wceq
    #
    cP
    cQ
    cP
    cQ
    wceq
    #
    @12
    @5
    @13
    @8
    @11
    cW
    c.an
    @13
    cP
    cQ
    @7
    @10
    c.or
    @13
    id
    @13
    @6
    @9
    cF
    cP
    cQ
    cG
    fveq2
    fveq2d
    oveq12d
    oveq1d
    adantl
    @5
    cP
    cQ
    wne
    #
    wa
    @0
    @1
    @2
    @3
    @14
    @12
    @0
    @1
    @4
    @14
    simpl1
    @0
    @1
    @4
    @14
    simpl2
    @2
    @3
    @0
    @1
    @14
    simpl3l
    @2
    @3
    @0
    @1
    @14
    simpl3r
    @5
    @14
    simpr
    cA
    cP
    cQ
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg35.l
    cdlemg35.j
    cdlemg35.m
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    @15
    eqid
    cdlemg39
    syl113anc
    pm2.61dane
end
