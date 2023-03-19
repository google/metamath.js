include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cbl.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "wss.mm"
include "cxr.mm"
include "cxp.mm"
include "wf.mm"
include "blf.mm"
include "frn.mm"
include "syl.mm"
include "sspwuni.mm"
include "sylib.mm"
include "cv.mm"
include "wa.mm"
include "c1.mm"
include "co.mm"
include "crp.mm"
include "1rp.mm"
include "blcntr.mm"
include "mp3an3.mm"
include "rpxr.mm"
include "ax-mp.mm"
include "blelrn.mm"
include "elunii.mm"
include "syl2anc.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem unirnbl
  let cD: class D
  let cX: class X
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cR: class R
  let cP: class P
  let cS: class S


  assert |- ( D e. ( *Met ` X ) -> U. ran ( ball ` D ) = X )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cbl
    cfv
    #
    crn
    #
    cuni
    #
    cX
    @0
    @2
    cX
    cpw
    #
    wss
    #
    @3
    cX
    wss
    @0
    cX
    cxr
    cxp
    #
    @4
    @1
    wf
    @5
    cD
    cX
    blf
    @6
    @4
    @1
    frn
    syl
    @2
    cX
    sspwuni
    sylib
    @0
    vx
    cX
    @3
    @0
    vx
    cv
    #
    cX
    wcel
    #
    @7
    @3
    wcel
    #
    @0
    @8
    wa
    @7
    @7
    c1
    @1
    co
    #
    wcel
    #
    @10
    @2
    wcel
    #
    @9
    @0
    @8
    c1
    crp
    wcel
    #
    @11
    1rp
    cD
    @7
    c1
    cX
    blcntr
    mp3an3
    @0
    @8
    c1
    cxr
    wcel
    #
    @12
    @13
    @14
    1rp
    c1
    rpxr
    ax-mp
    cD
    @7
    c1
    cX
    blelrn
    mp3an3
    @7
    @10
    @2
    elunii
    syl2anc
    ex
    ssrdv
    eqssd
end
