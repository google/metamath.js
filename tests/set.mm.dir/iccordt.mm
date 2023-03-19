include "cicc.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "cle.mm"
include "cordt.mm"
include "ccld.mm"
include "df-ov.mm"
include "cxr.mm"
include "cxp.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "crab.mm"
include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "ctsr.mm"
include "letsr.mm"
include "ledm.mm"
include "ordtcld3.mm"
include "mp3an1.mm"
include "rgen2a.mm"
include "df-icc.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "ctop.mm"
include "c0.mm"
include "letop.mm"
include "0cld.mm"
include "ax-mp.mm"
include "f0cli.mm"
include "eqeltri.mm"

theorem iccordt
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A [,] B ) e. ( Clsd ` ( ordTop ` <_ ) )

  proof
    cA
    cB
    cicc
    co
    cA
    cB
    cop
    #
    cicc
    cfv
    cle
    cordt
    cfv
    #
    ccld
    cfv
    #
    cA
    cB
    cicc
    df-ov
    cxr
    cxr
    cxp
    #
    @2
    @0
    cicc
    vx
    cv
    #
    vz
    cv
    #
    cle
    wbr
    @5
    vy
    cv
    #
    cle
    wbr
    wa
    vz
    cxr
    crab
    #
    @2
    wcel
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    @3
    @2
    cicc
    wf
    @8
    vx
    vy
    cxr
    cle
    ctsr
    wcel
    @4
    cxr
    wcel
    @6
    cxr
    wcel
    @8
    letsr
    vz
    @4
    @6
    cle
    ctsr
    cxr
    ledm
    ordtcld3
    mp3an1
    rgen2a
    vx
    vy
    cxr
    cxr
    @7
    @2
    cicc
    vx
    vy
    vz
    df-icc
    fmpt2
    mpbi
    @1
    ctop
    wcel
    c0
    @2
    wcel
    letop
    @1
    0cld
    ax-mp
    f0cli
    eqeltri
end
