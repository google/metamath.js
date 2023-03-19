include "wss.mm"
include "cdm.mm"
include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "cuni.mm"
include "cmpt.mm"
include "ccom.mm"
include "ctpos.mm"
include "coss1.mm"
include "cres.mm"
include "wceq.mm"
include "dmss.mm"
include "cnvss.mm"
include "unss1.mm"
include "resmpt.mm"
include "4syl.mm"
include "resss.mm"
include "syl6eqssr.mm"
include "coss2.mm"
include "syl.mm"
include "sstrd.mm"
include "df-tpos.mm"
include "3sstr4g.mm"

theorem tposss
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z


  assert |- ( F C_ G -> tpos F C_ tpos G )

  proof
    cF
    cG
    wss
    #
    cF
    vx
    cF
    cdm
    #
    ccnv
    #
    c0
    csn
    #
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
    cG
    vx
    cG
    cdm
    #
    ccnv
    #
    @3
    cun
    #
    @5
    cmpt
    #
    ccom
    #
    cF
    ctpos
    cG
    ctpos
    @0
    @7
    cG
    @6
    ccom
    #
    @12
    cF
    cG
    @6
    coss1
    @0
    @6
    @11
    wss
    @13
    @12
    wss
    @0
    @6
    @11
    @4
    cres
    #
    @11
    @0
    @1
    @8
    wss
    @2
    @9
    wss
    @4
    @10
    wss
    @14
    @6
    wceq
    cF
    cG
    dmss
    @1
    @8
    cnvss
    @2
    @9
    @3
    unss1
    vx
    @10
    @4
    @5
    resmpt
    4syl
    @11
    @4
    resss
    syl6eqssr
    @6
    @11
    cG
    coss2
    syl
    sstrd
    vx
    cF
    df-tpos
    vx
    cG
    df-tpos
    3sstr4g
end
