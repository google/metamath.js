include "wcel.mm"
include "cpw.mm"
include "c1stc.mm"
include "clly.mm"
include "cv.mm"
include "csn.mm"
include "wral.mm"
include "c2ndc.mm"
include "ctg.mm"
include "cfv.mm"
include "ctop.mm"
include "wceq.mm"
include "cvv.mm"
include "snex.mm"
include "distop.mm"
include "ax-mp.mm"
include "tgtop.mm"
include "ctb.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "topbas.mm"
include "csdm.mm"
include "cfn.mm"
include "snfi.mm"
include "pwfi.mm"
include "mpbi.mm"
include "isfinite.mm"
include "sdomdom.mm"
include "2ndci.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "2ndc1stc.mm"
include "rgenw.mm"
include "dislly.mm"
include "mpbiri.mm"
include "lly1stc.mm"
include "syl6eleq.mm"

theorem dis1stc
  let cV: class V
  let cX: class X
  let va: setvar a
  let vj: setvar j
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let cA: class A
  let cJ: class J


  assert |- ( X e. V -> ~P X e. 1stc )

  proof
    cX
    cV
    wcel
    #
    cX
    cpw
    #
    c1stc
    clly
    #
    c1stc
    @0
    @1
    @2
    wcel
    vx
    cv
    #
    csn
    #
    cpw
    #
    c1stc
    wcel
    #
    vx
    cX
    wral
    @6
    vx
    cX
    @5
    c2ndc
    wcel
    @6
    @5
    ctg
    cfv
    #
    @5
    c2ndc
    @5
    ctop
    wcel
    #
    @7
    @5
    wceq
    @4
    cvv
    wcel
    @8
    @3
    snex
    @4
    cvv
    distop
    ax-mp
    #
    @5
    tgtop
    ax-mp
    @5
    ctb
    wcel
    #
    @5
    com
    cdom
    wbr
    #
    @7
    c2ndc
    wcel
    @8
    @10
    @9
    @5
    topbas
    ax-mp
    @5
    com
    csdm
    wbr
    #
    @11
    @5
    cfn
    wcel
    #
    @12
    @4
    cfn
    wcel
    @13
    @3
    snfi
    @4
    pwfi
    mpbi
    @5
    isfinite
    mpbi
    @5
    com
    sdomdom
    ax-mp
    @5
    2ndci
    mp2an
    eqeltrri
    @5
    2ndc1stc
    ax-mp
    rgenw
    vx
    c1stc
    cV
    cX
    dislly
    mpbiri
    lly1stc
    syl6eleq
end
