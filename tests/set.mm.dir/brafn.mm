include "chil.mm"
include "wcel.mm"
include "cc.mm"
include "cbr.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cmpt.mm"
include "hicl.mm"
include "ancoms.mm"
include "eqid.mm"
include "fmptd.mm"
include "brafval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem brafn
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T


  assert |- ( A e. ~H -> ( bra ` A ) : ~H --> CC )

  proof
    cA
    chil
    wcel
    #
    chil
    cc
    cA
    cbr
    cfv
    #
    wf
    chil
    cc
    vx
    chil
    vx
    cv
    #
    cA
    csp
    co
    #
    cmpt
    #
    wf
    @0
    vx
    chil
    @3
    cc
    @4
    @2
    chil
    wcel
    @0
    @3
    cc
    wcel
    @2
    cA
    hicl
    ancoms
    @4
    eqid
    fmptd
    @0
    chil
    cc
    @1
    @4
    vx
    cA
    brafval
    feq1d
    mpbird
end
