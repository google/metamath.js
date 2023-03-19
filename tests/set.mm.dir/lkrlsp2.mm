include "clvec.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wn.mm"
include "csca.mm"
include "c0g.mm"
include "wne.mm"
include "csn.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "simp2l.mm"
include "simp3.mm"
include "wb.mm"
include "simp1.mm"
include "simp2r.mm"
include "eqid.mm"
include "ellkr.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "3expia.mm"
include "necon3bd.mm"
include "3impia.mm"
include "lkrlsp.mm"
include "syld3an3.mm"

theorem lkrlsp2
  let c.po: class .(+)
  let cF: class F
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lkrlsp2.v: |- V = ( Base ` W )
  assume lkrlsp2.n: |- N = ( LSpan ` W )
  assume lkrlsp2.p: |- .(+) = ( LSSum ` W )
  assume lkrlsp2.f: |- F = ( LFnl ` W )
  assume lkrlsp2.k: |- K = ( LKer ` W )


  assert |- ( ( W e. LVec /\ ( X e. V /\ G e. F ) /\ -. X e. ( K ` G ) ) -> ( ( K ` G ) .(+) ( N ` { X } ) ) = V )

  proof
    cW
    clvec
    wcel
    #
    cX
    cV
    wcel
    #
    cG
    cF
    wcel
    #
    wa
    #
    cX
    cG
    cK
    cfv
    #
    wcel
    #
    wn
    #
    cX
    cG
    cfv
    #
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wne
    #
    @4
    cX
    csn
    cN
    cfv
    c.po
    co
    cV
    wceq
    @0
    @3
    @6
    @10
    @0
    @3
    wa
    @5
    @7
    @9
    @0
    @3
    @7
    @9
    wceq
    #
    @5
    @0
    @3
    @11
    w3a
    #
    @5
    @1
    @11
    @0
    @1
    @2
    @11
    simp2l
    @0
    @3
    @11
    simp3
    @12
    @0
    @2
    @5
    @1
    @11
    wa
    wb
    @0
    @3
    @11
    simp1
    @0
    @1
    @2
    @11
    simp2r
    @8
    cF
    cG
    cK
    cV
    cW
    cX
    clvec
    @9
    lkrlsp2.v
    @8
    eqid
    #
    @9
    eqid
    #
    lkrlsp2.f
    lkrlsp2.k
    ellkr
    syl2anc
    mpbir2and
    3expia
    necon3bd
    3impia
    @8
    c.po
    cF
    cG
    cK
    cN
    cV
    cW
    cX
    @9
    @13
    @14
    lkrlsp2.v
    lkrlsp2.n
    lkrlsp2.p
    lkrlsp2.f
    lkrlsp2.k
    lkrlsp
    syld3an3
end
