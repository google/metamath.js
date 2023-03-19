include "wcel.mm"
include "wa.mm"
include "cof.mm"
include "co.mm"
include "cvv.mm"
include "cxp.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "ccnv.mm"
include "cuni.mm"
include "cmpt.mm"
include "ccom.mm"
include "ctpos.mm"
include "wfun.mm"
include "wceq.mm"
include "elex.mm"
include "adantr.mm"
include "adantl.mm"
include "funmpt.mm"
include "a1i.mm"
include "dftpos4.mm"
include "tposexg.mm"
include "syl5eqelr.mm"
include "ofco2.mm"
include "syl23anc.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"

theorem oftpos
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cH: class H


  assert |- ( ( F e. V /\ G e. W ) -> tpos ( F oF R G ) = ( tpos F oF R tpos G ) )

  proof
    cF
    cV
    wcel
    #
    cG
    cW
    wcel
    #
    wa
    #
    cF
    cG
    cR
    cof
    #
    co
    #
    vx
    cvv
    cvv
    cxp
    c0
    csn
    cun
    #
    vx
    cv
    csn
    ccnv
    cuni
    #
    cmpt
    #
    ccom
    #
    cF
    @7
    ccom
    #
    cG
    @7
    ccom
    #
    @3
    co
    #
    @4
    ctpos
    cF
    ctpos
    #
    cG
    ctpos
    #
    @3
    co
    @2
    cF
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    @7
    wfun
    #
    @9
    cvv
    wcel
    @10
    cvv
    wcel
    @8
    @11
    wceq
    @0
    @14
    @1
    cF
    cV
    elex
    adantr
    @1
    @15
    @0
    cG
    cW
    elex
    adantl
    @16
    @2
    vx
    @5
    @6
    funmpt
    a1i
    @2
    @9
    @12
    cvv
    vx
    cF
    dftpos4
    #
    @0
    @12
    cvv
    wcel
    @1
    cF
    cV
    tposexg
    adantr
    syl5eqelr
    @2
    @10
    @13
    cvv
    vx
    cG
    dftpos4
    #
    @1
    @13
    cvv
    wcel
    @0
    cG
    cW
    tposexg
    adantl
    syl5eqelr
    cR
    cF
    cG
    @7
    ofco2
    syl23anc
    vx
    @4
    dftpos4
    @12
    @9
    @13
    @10
    @3
    @17
    @18
    oveq12i
    3eqtr4g
end
