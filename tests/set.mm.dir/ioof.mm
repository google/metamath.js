include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "crab.mm"
include "cr.mm"
include "cpw.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cioo.mm"
include "wf.mm"
include "co.mm"
include "iooval.mm"
include "wss.mm"
include "ioossre.mm"
include "ovex.mm"
include "elpw.mm"
include "mpbir.mm"
include "syl6eqelr.mm"
include "rgen2a.mm"
include "df-ioo.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem ioof
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- (,) : ( RR* X. RR* ) --> ~P RR

  proof
    vx
    cv
    #
    vz
    cv
    #
    clt
    wbr
    @1
    vy
    cv
    #
    clt
    wbr
    wa
    vz
    cxr
    crab
    #
    cr
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
    @4
    cioo
    wf
    @5
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
    @3
    @0
    @2
    cioo
    co
    #
    @4
    vz
    @0
    @2
    iooval
    @6
    @4
    wcel
    @6
    cr
    wss
    @0
    @2
    ioossre
    @6
    cr
    @0
    @2
    cioo
    ovex
    elpw
    mpbir
    syl6eqelr
    rgen2a
    vx
    vy
    cxr
    cxr
    @3
    @4
    cioo
    vx
    vy
    vz
    df-ioo
    fmpt2
    mpbi
end
