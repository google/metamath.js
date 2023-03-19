include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cfv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "wceq.mm"
include "setsval.mm"
include "3adant2.mm"
include "fveq1d.mm"
include "cdm.mm"
include "wn.mm"
include "simp2.mm"
include "simp3.mm"
include "neldifsn.mm"
include "cin.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sseli.mm"
include "mto.mm"
include "a1i.mm"
include "fsnunfv.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem fvsetsid
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( F e. V /\ X e. W /\ Y e. U ) -> ( ( F sSet <. X , Y >. ) ` X ) = Y )

  proof
    cF
    cV
    wcel
    #
    cX
    cW
    wcel
    #
    cY
    cU
    wcel
    #
    w3a
    #
    cX
    cF
    cX
    cY
    cop
    #
    csts
    co
    #
    cfv
    cX
    cF
    cvv
    cX
    csn
    cdif
    #
    cres
    #
    @4
    csn
    cun
    #
    cfv
    #
    cY
    @3
    cX
    @5
    @8
    @0
    @2
    @5
    @8
    wceq
    @1
    cX
    cY
    cF
    cV
    cU
    setsval
    3adant2
    fveq1d
    @3
    @1
    @2
    cX
    @7
    cdm
    #
    wcel
    #
    wn
    #
    @9
    cY
    wceq
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @12
    @3
    @11
    cX
    @6
    wcel
    cX
    cvv
    neldifsn
    @10
    @6
    cX
    @10
    @6
    cF
    cdm
    #
    cin
    @6
    cF
    @6
    dmres
    @6
    @13
    inss1
    eqsstri
    sseli
    mto
    a1i
    @7
    cW
    cU
    cX
    cY
    fsnunfv
    syl3anc
    eqtrd
end
