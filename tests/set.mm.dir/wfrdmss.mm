include "cdm.mm"
include "cv.mm"
include "wfn.mm"
include "wss.mm"
include "cpred.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "ciun.mm"
include "cuni.mm"
include "cwrecs.mm"
include "df-wrecs.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "dmuni.mm"
include "iunss.mm"
include "eqid.mm"
include "wfrlem3.mm"
include "mprgbir.mm"
include "eqsstri.mm"

theorem wfrdmss
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume wfrlem6.1: |- F = wrecs ( R , A , G )


  assert |- dom F C_ A

  proof
    cF
    cdm
    #
    vg
    vf
    cv
    #
    vx
    cv
    #
    wfn
    @2
    cA
    wss
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @2
    wss
    vy
    @2
    wral
    wa
    @3
    @1
    cfv
    @1
    @4
    cres
    cG
    cfv
    wceq
    vy
    @2
    wral
    w3a
    vx
    wex
    vf
    cab
    #
    vg
    cv
    cdm
    #
    ciun
    #
    cA
    @0
    @5
    cuni
    #
    cdm
    @7
    cF
    @8
    cF
    cA
    cR
    cG
    cwrecs
    @8
    wfrlem6.1
    vx
    vy
    cA
    cR
    vf
    cG
    df-wrecs
    eqtri
    dmeqi
    vg
    @5
    dmuni
    eqtri
    @7
    cA
    wss
    @6
    cA
    wss
    vg
    @5
    vg
    @5
    @6
    cA
    iunss
    vx
    vy
    cA
    @5
    cR
    vf
    vg
    cG
    @5
    eqid
    wfrlem3
    mprgbir
    eqsstri
end
