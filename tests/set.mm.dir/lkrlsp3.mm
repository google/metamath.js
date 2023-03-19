include "clvec.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wn.mm"
include "w3a.mm"
include "csn.mm"
include "cun.mm"
include "clsm.mm"
include "co.mm"
include "clmod.mm"
include "clss.mm"
include "wceq.mm"
include "lveclmod.mm"
include "3ad2ant1.mm"
include "simp2r.mm"
include "eqid.mm"
include "lkrlss.mm"
include "syl2anc.mm"
include "lspid.mm"
include "uneq1d.mm"
include "fveq2d.mm"
include "wss.mm"
include "lkrssv.mm"
include "simp2l.mm"
include "snssd.mm"
include "lspun.mm"
include "syl3anc.mm"
include "lspsncl.mm"
include "lsmsp.mm"
include "3eqtr4d.mm"
include "lkrlsp2.mm"
include "eqtrd.mm"

theorem lkrlsp3
  let cF: class F
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lkrlsp3.v: |- V = ( Base ` W )
  assume lkrlsp3.n: |- N = ( LSpan ` W )
  assume lkrlsp3.f: |- F = ( LFnl ` W )
  assume lkrlsp3.k: |- K = ( LKer ` W )


  assert |- ( ( W e. LVec /\ ( X e. V /\ G e. F ) /\ -. X e. ( K ` G ) ) -> ( N ` ( ( K ` G ) u. { X } ) ) = V )

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
    wn
    #
    w3a
    #
    @4
    cX
    csn
    #
    cun
    cN
    cfv
    #
    @4
    @7
    cN
    cfv
    #
    cW
    clsm
    cfv
    #
    co
    #
    cV
    @6
    @4
    cN
    cfv
    #
    @9
    cun
    #
    cN
    cfv
    #
    @4
    @9
    cun
    #
    cN
    cfv
    #
    @8
    @11
    @6
    @13
    @15
    cN
    @6
    @12
    @4
    @9
    @6
    cW
    clmod
    wcel
    #
    @4
    cW
    clss
    cfv
    #
    wcel
    #
    @12
    @4
    wceq
    @0
    @3
    @17
    @5
    cW
    lveclmod
    3ad2ant1
    #
    @6
    @17
    @2
    @19
    @20
    @0
    @1
    @2
    @5
    simp2r
    #
    @18
    cF
    cG
    cK
    cW
    lkrlsp3.f
    lkrlsp3.k
    @18
    eqid
    #
    lkrlss
    syl2anc
    #
    @18
    @4
    cN
    cW
    @22
    lkrlsp3.n
    lspid
    syl2anc
    uneq1d
    fveq2d
    @6
    @17
    @4
    cV
    wss
    @7
    cV
    wss
    @8
    @14
    wceq
    @20
    @6
    cF
    cG
    cK
    cV
    cW
    lkrlsp3.v
    lkrlsp3.f
    lkrlsp3.k
    @20
    @21
    lkrssv
    @6
    cX
    cV
    @0
    @1
    @2
    @5
    simp2l
    #
    snssd
    @4
    @7
    cN
    cV
    cW
    lkrlsp3.v
    lkrlsp3.n
    lspun
    syl3anc
    @6
    @17
    @19
    @9
    @18
    wcel
    #
    @11
    @16
    wceq
    @20
    @23
    @6
    @17
    @1
    @25
    @20
    @24
    @18
    cN
    cV
    cW
    cX
    lkrlsp3.v
    @22
    lkrlsp3.n
    lspsncl
    syl2anc
    @10
    @18
    @4
    @9
    cN
    cW
    @22
    lkrlsp3.n
    @10
    eqid
    #
    lsmsp
    syl3anc
    3eqtr4d
    @10
    cF
    cG
    cK
    cN
    cV
    cW
    cX
    lkrlsp3.v
    lkrlsp3.n
    @26
    lkrlsp3.f
    lkrlsp3.k
    lkrlsp2
    eqtrd
end
