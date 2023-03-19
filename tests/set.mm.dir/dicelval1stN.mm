include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "w3a.mm"
include "ctendo.mm"
include "cxp.mm"
include "c1st.mm"
include "cdvh.mm"
include "cbs.mm"
include "eqid.mm"
include "dicssdvh.mm"
include "wceq.mm"
include "dvhvbase.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "sseld.mm"
include "3impia.mm"
include "xp1st.mm"
include "syl.mm"

theorem dicelval1stN
  let cA: class A
  let cQ: class Q
  let cT: class T
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cY: class Y
  assume dicelval1st.l: |- .<_ = ( le ` K )
  assume dicelval1st.a: |- A = ( Atoms ` K )
  assume dicelval1st.h: |- H = ( LHyp ` K )
  assume dicelval1st.t: |- T = ( ( LTrn ` K ) ` W )
  assume dicelval1st.i: |- I = ( ( DIsoC ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ Y e. ( I ` Q ) ) -> ( 1st ` Y ) e. T )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cY
    cQ
    cI
    cfv
    #
    wcel
    #
    w3a
    cY
    cT
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cxp
    #
    wcel
    #
    cY
    c1st
    cfv
    cT
    wcel
    @0
    @1
    @3
    @6
    @0
    @1
    wa
    #
    @2
    @5
    cY
    @7
    @2
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cbs
    cfv
    #
    @5
    cA
    cQ
    @8
    cH
    cI
    cK
    c.le
    @9
    cW
    dicelval1st.l
    dicelval1st.a
    dicelval1st.h
    dicelval1st.i
    @8
    eqid
    #
    @9
    eqid
    #
    dicssdvh
    @0
    @9
    @5
    wceq
    @1
    cT
    @8
    @4
    cH
    cK
    @9
    cW
    chlt
    dicelval1st.h
    dicelval1st.t
    @4
    eqid
    @10
    @11
    dvhvbase
    adantr
    sseqtrd
    sseld
    3impia
    cY
    cT
    @4
    xp1st
    syl
end
