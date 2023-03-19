include "wrel.mm"
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
include "cuni.mm"
include "reluni.mm"
include "wcel.mm"
include "wfun.mm"
include "eqid.mm"
include "wfrlem2.mm"
include "funrel.mm"
include "syl.mm"
include "mprgbir.mm"
include "cwrecs.mm"
include "df-wrecs.mm"
include "eqtri.mm"
include "releqi.mm"
include "mpbir.mm"

theorem wfrrel
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


  assert |- Rel F

  proof
    cF
    wrel
    vf
    cv
    #
    vx
    cv
    #
    wfn
    @1
    cA
    wss
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @1
    wss
    vy
    @1
    wral
    wa
    @2
    @0
    cfv
    @0
    @3
    cres
    cG
    cfv
    wceq
    vy
    @1
    wral
    w3a
    vx
    wex
    vf
    cab
    #
    cuni
    #
    wrel
    #
    @6
    vg
    cv
    #
    wrel
    #
    vg
    @4
    vg
    @4
    reluni
    @7
    @4
    wcel
    @7
    wfun
    @8
    vx
    vy
    cA
    @4
    cR
    vf
    vg
    cG
    @4
    eqid
    wfrlem2
    @7
    funrel
    syl
    mprgbir
    cF
    @5
    cF
    cA
    cR
    cG
    cwrecs
    @5
    wfrlem6.1
    vx
    vy
    cA
    cR
    vf
    cG
    df-wrecs
    eqtri
    releqi
    mpbir
end
