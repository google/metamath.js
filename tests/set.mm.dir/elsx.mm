include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cv.mm"
include "cmpt2.mm"
include "crn.mm"
include "csigagen.mm"
include "cfv.mm"
include "csx.mm"
include "co.mm"
include "wss.mm"
include "cvv.mm"
include "eqid.mm"
include "txbasex.mm"
include "sssigagen.mm"
include "syl.mm"
include "adantr.mm"
include "wceq.mm"
include "wrex.mm"
include "xpeq1.mm"
include "eqeq2d.mm"
include "xpeq2.mm"
include "rspc2ev.mm"
include "mp3an3.mm"
include "wb.mm"
include "xpexg.mm"
include "elrnmpt2g.mm"
include "mpbird.mm"
include "adantl.mm"
include "sseldd.mm"
include "sxval.mm"
include "eleqtrrd.mm"

theorem elsx
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( S e. V /\ T e. W ) /\ ( A e. S /\ B e. T ) ) -> ( A X. B ) e. ( S sX T ) )

  proof
    cS
    cV
    wcel
    cT
    cW
    wcel
    wa
    #
    cA
    cS
    wcel
    #
    cB
    cT
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cxp
    #
    vx
    vy
    cS
    cT
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    csigagen
    cfv
    #
    cS
    cT
    csx
    co
    #
    @4
    @10
    @11
    @5
    @0
    @10
    @11
    wss
    #
    @3
    @0
    @10
    cvv
    wcel
    @13
    vx
    vy
    @10
    cS
    cT
    cV
    cW
    @10
    eqid
    #
    txbasex
    @10
    cvv
    sssigagen
    syl
    adantr
    @3
    @5
    @10
    wcel
    #
    @0
    @3
    @15
    @5
    @8
    wceq
    #
    vy
    cT
    wrex
    vx
    cS
    wrex
    #
    @1
    @2
    @5
    @5
    wceq
    #
    @17
    @5
    eqid
    @16
    @18
    @5
    cA
    @7
    cxp
    #
    wceq
    vx
    vy
    cA
    cB
    cS
    cT
    @6
    cA
    wceq
    @8
    @19
    @5
    @6
    cA
    @7
    xpeq1
    eqeq2d
    @7
    cB
    wceq
    @19
    @5
    @5
    @7
    cB
    cA
    xpeq2
    eqeq2d
    rspc2ev
    mp3an3
    @3
    @5
    cvv
    wcel
    @15
    @17
    wb
    cA
    cB
    cS
    cT
    xpexg
    vx
    vy
    cS
    cT
    @8
    @5
    @9
    cvv
    @9
    eqid
    elrnmpt2g
    syl
    mpbird
    adantl
    sseldd
    @0
    @12
    @11
    wceq
    @3
    vx
    vy
    @10
    cS
    cT
    cV
    cW
    @14
    sxval
    adantr
    eleqtrrd
end
