include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "csn.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wss.mm"
include "wa.mm"
include "snfi.mm"
include "snopsuppss.mm"
include "pm3.2i.mm"
include "ssfi.mm"
include "mp1i.mm"
include "wfun.mm"
include "cvv.mm"
include "wb.mm"
include "funsng.mm"
include "3adant3.mm"
include "snex.mm"
include "a1i.mm"
include "simp3.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem snopfsupp
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( ( X e. V /\ Y e. W /\ Z e. U ) -> { <. X , Y >. } finSupp Z )

  proof
    cX
    cV
    wcel
    #
    cY
    cW
    wcel
    #
    cZ
    cU
    wcel
    #
    w3a
    #
    cX
    cY
    cop
    #
    csn
    #
    cZ
    cfsupp
    wbr
    #
    @5
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    cX
    csn
    #
    cfn
    wcel
    #
    @7
    @9
    wss
    #
    wa
    @8
    @3
    @10
    @11
    cX
    snfi
    cX
    cY
    cZ
    snopsuppss
    pm3.2i
    @9
    @7
    ssfi
    mp1i
    @3
    @5
    wfun
    #
    @5
    cvv
    wcel
    #
    @2
    @6
    @8
    wb
    @0
    @1
    @12
    @2
    cX
    cY
    cV
    cW
    funsng
    3adant3
    @13
    @3
    @4
    snex
    a1i
    @0
    @1
    @2
    simp3
    @5
    cvv
    cU
    cZ
    funisfsupp
    syl3anc
    mpbird
end
