include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "wi.mm"
include "simpll.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2l.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simpr3l.mm"
include "eqid.mm"
include "trlcl.mm"
include "syldan.mm"
include "ltrnel.mm"
include "3adant3r3.mm"
include "trlnle.mm"
include "hlexch2.mm"
include "syl131anc.mm"
include "wceq.mm"
include "trljat2.mm"
include "breq2d.mm"
include "sylibd.mm"

theorem cdlemc3
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemc3.l: |- .<_ = ( le ` K )
  assume cdlemc3.j: |- .\/ = ( join ` K )
  assume cdlemc3.m: |- ./\ = ( meet ` K )
  assume cdlemc3.a: |- A = ( Atoms ` K )
  assume cdlemc3.h: |- H = ( LHyp ` K )
  assume cdlemc3.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemc3.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) ) -> ( ( F ` P ) .<_ ( Q .\/ ( R ` F ) ) -> Q .<_ ( P .\/ ( F ` P ) ) ) )

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
    cF
    cT
    wcel
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
    w3a
    #
    wa
    #
    cP
    cF
    cfv
    #
    cQ
    cF
    cR
    cfv
    #
    c.or
    co
    c.le
    wbr
    #
    cQ
    @12
    @13
    c.or
    co
    #
    c.le
    wbr
    #
    cQ
    cP
    @12
    c.or
    co
    #
    c.le
    wbr
    @11
    @0
    @12
    cA
    wcel
    #
    @7
    @13
    cK
    cbs
    cfv
    #
    wcel
    #
    @12
    @13
    c.le
    wbr
    wn
    #
    @14
    @16
    wi
    @0
    @1
    @10
    simpll
    @11
    @2
    @3
    @4
    @18
    @2
    @10
    simpl
    #
    @2
    @3
    @6
    @9
    simpr1
    #
    @4
    @5
    @3
    @9
    @2
    simpr2l
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemc3.l
    cdlemc3.a
    cdlemc3.h
    cdlemc3.t
    ltrnat
    syl3anc
    @7
    @8
    @3
    @6
    @2
    simpr3l
    @2
    @10
    @3
    @20
    @23
    @19
    cR
    cT
    cF
    cH
    cK
    cW
    @19
    eqid
    #
    cdlemc3.h
    cdlemc3.t
    cdlemc3.r
    trlcl
    syldan
    @11
    @2
    @3
    @18
    @12
    cW
    c.le
    wbr
    wn
    wa
    #
    @21
    @22
    @23
    @2
    @3
    @6
    @25
    @9
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemc3.l
    cdlemc3.a
    cdlemc3.h
    cdlemc3.t
    ltrnel
    3adant3r3
    cA
    @12
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemc3.l
    cdlemc3.a
    cdlemc3.h
    cdlemc3.t
    cdlemc3.r
    trlnle
    syl3anc
    cA
    @19
    @12
    cQ
    c.or
    cK
    c.le
    @13
    @24
    cdlemc3.l
    cdlemc3.j
    cdlemc3.a
    hlexch2
    syl131anc
    @11
    @15
    @17
    cQ
    c.le
    @2
    @3
    @6
    @15
    @17
    wceq
    @9
    cA
    cP
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    cW
    cdlemc3.l
    cdlemc3.j
    cdlemc3.a
    cdlemc3.h
    cdlemc3.t
    cdlemc3.r
    trljat2
    3adant3r3
    breq2d
    sylibd
end
