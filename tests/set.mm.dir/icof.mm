include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cxr.mm"
include "crab.mm"
include "cpw.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cico.mm"
include "wf.mm"
include "eqidd.mm"
include "wss.mm"
include "ssrab2.mm"
include "xrex.mm"
include "rabex.mm"
include "elpw.mm"
include "mpbir.mm"
include "syl6eqelr.mm"
include "rgen2a.mm"
include "df-ico.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem icof
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- [,) : ( RR* X. RR* ) --> ~P RR*

  proof
    vx
    cv
    #
    vz
    cv
    #
    cle
    wbr
    @1
    vy
    cv
    #
    clt
    wbr
    wa
    #
    vz
    cxr
    crab
    #
    cxr
    cpw
    #
    wcel
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    cxr
    cxr
    cxp
    @5
    cico
    wf
    @6
    vx
    vy
    cxr
    @0
    cxr
    wcel
    @2
    cxr
    wcel
    wa
    #
    @4
    @4
    @5
    @7
    @4
    eqidd
    @6
    @4
    cxr
    wss
    @3
    vz
    cxr
    ssrab2
    @4
    cxr
    @3
    vz
    cxr
    xrex
    rabex
    elpw
    mpbir
    syl6eqelr
    rgen2a
    vx
    vy
    cxr
    cxr
    @4
    @5
    cico
    vx
    vy
    vz
    df-ico
    fmpt2
    mpbi
end
