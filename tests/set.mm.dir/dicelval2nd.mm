include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "w3a.mm"
include "cltrn.mm"
include "cxp.mm"
include "c2nd.mm"
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
include "xp2nd.mm"
include "syl.mm"

theorem dicelval2nd
  let cA: class A
  let cQ: class Q
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cY: class Y
  assume dicelval2nd.l: |- .<_ = ( le ` K )
  assume dicelval2nd.a: |- A = ( Atoms ` K )
  assume dicelval2nd.h: |- H = ( LHyp ` K )
  assume dicelval2nd.e: |- E = ( ( TEndo ` K ) ` W )
  assume dicelval2nd.i: |- I = ( ( DIsoC ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ Y e. ( I ` Q ) ) -> ( 2nd ` Y ) e. E )

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
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cE
    cxp
    #
    wcel
    #
    cY
    c2nd
    cfv
    cE
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
    dicelval2nd.l
    dicelval2nd.a
    dicelval2nd.h
    dicelval2nd.i
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
    @4
    @8
    cE
    cH
    cK
    @9
    cW
    chlt
    dicelval2nd.h
    @4
    eqid
    dicelval2nd.e
    @10
    @11
    dvhvbase
    adantr
    sseqtrd
    sseld
    3impia
    cY
    @4
    cE
    xp2nd
    syl
end
