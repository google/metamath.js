include "wfun.mm"
include "cba.mm"
include "cfv.mm"
include "cv.mm"
include "wf.mm"
include "cdip.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "copab.mm"
include "wmo.mm"
include "funopab.mm"
include "wa.mm"
include "eqid.mm"
include "ajmoi.mm"
include "3simpc.mm"
include "moimi.mm"
include "ax-mp.mm"
include "mpgbir.mm"
include "cnv.mm"
include "wcel.mm"
include "phnvi.mm"
include "ajfval.mm"
include "mp2an.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem ajfuni
  let cA: class A
  let cU: class U
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  assume ajfuni.5: |- A = ( U adj W )
  assume ajfuni.u: |- U e. CPreHilOLD
  assume ajfuni.w: |- W e. NrmCVec


  assert |- Fun A

  proof
    cA
    wfun
    cU
    cba
    cfv
    #
    cW
    cba
    cfv
    #
    vt
    cv
    #
    wf
    #
    @1
    @0
    vs
    cv
    #
    wf
    #
    vx
    cv
    #
    @2
    cfv
    vy
    cv
    #
    cW
    cdip
    cfv
    #
    co
    @6
    @7
    @4
    cfv
    cU
    cdip
    cfv
    #
    co
    wceq
    vy
    @1
    wral
    vx
    @0
    wral
    #
    w3a
    #
    vt
    vs
    copab
    #
    wfun
    #
    @13
    @11
    vs
    wmo
    #
    vt
    @11
    vt
    vs
    funopab
    @5
    @10
    wa
    #
    vs
    wmo
    @14
    vx
    vy
    @9
    @8
    @2
    cU
    @0
    @1
    vs
    @0
    eqid
    #
    @9
    eqid
    #
    ajfuni.u
    ajmoi
    @11
    @15
    vs
    @3
    @5
    @10
    3simpc
    moimi
    ax-mp
    mpgbir
    cA
    @12
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    cA
    @12
    wceq
    cU
    ajfuni.u
    phnvi
    ajfuni.w
    vx
    vy
    vt
    cA
    @9
    @8
    cU
    cW
    @0
    @1
    vs
    @16
    @1
    eqid
    @17
    @8
    eqid
    ajfuni.5
    ajfval
    mp2an
    funeqi
    mpbir
end
