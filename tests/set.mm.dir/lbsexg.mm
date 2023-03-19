include "wac.mm"
include "clvec.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wne.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "id.mm"
include "cvv.mm"
include "fvex.mm"
include "pwex.mm"
include "wceq.mm"
include "dfac10.mm"
include "biimpi.mm"
include "syl5eleqr.mm"
include "csn.mm"
include "cdif.mm"
include "clspn.mm"
include "wn.mm"
include "wral.mm"
include "0ss.mm"
include "ral0.mm"
include "eqid.mm"
include "lbsextg.mm"
include "mp3an23.mm"
include "syl2anr.mm"
include "rexn0.mm"
include "syl.mm"

theorem lbsexg
  let cJ: class J
  let cW: class W
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cN: class N
  let cV: class V
  assume lbsex.j: |- J = ( LBasis ` W )


  assert |- ( ( CHOICE /\ W e. LVec ) -> J =/= (/) )

  proof
    wac
    cW
    clvec
    wcel
    #
    wa
    c0
    vs
    cv
    wss
    #
    vs
    cJ
    wrex
    #
    cJ
    c0
    wne
    @0
    @0
    cW
    cbs
    cfv
    #
    cpw
    #
    ccrd
    cdm
    #
    wcel
    #
    @2
    wac
    @0
    id
    wac
    @4
    cvv
    @5
    @3
    cW
    cbs
    fvex
    pwex
    wac
    @5
    cvv
    wceq
    dfac10
    biimpi
    syl5eleqr
    @0
    @6
    wa
    c0
    @3
    wss
    vx
    cv
    #
    c0
    @7
    csn
    cdif
    cW
    clspn
    cfv
    #
    cfv
    wcel
    wn
    #
    vx
    c0
    wral
    @2
    @3
    0ss
    @9
    vx
    ral0
    vx
    c0
    cJ
    @8
    @3
    cW
    vs
    lbsex.j
    @3
    eqid
    @8
    eqid
    lbsextg
    mp3an23
    syl2anr
    @1
    vs
    cJ
    rexn0
    syl
end
