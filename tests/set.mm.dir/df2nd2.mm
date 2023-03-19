include "c2nd.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "copab.mm"
include "wcel.mm"
include "wa.mm"
include "coprab.mm"
include "cmpt.mm"
include "wfn.mm"
include "wfo.mm"
include "fo2nd.mm"
include "fofn.mm"
include "ax-mp.mm"
include "dffn5.mm"
include "mpbi.mm"
include "mptv.mm"
include "eqtri.mm"
include "reseq1i.mm"
include "resopab.mm"
include "cop.mm"
include "vex.mm"
include "op2ndd.mm"
include "eqeq2d.mm"
include "dfoprab3.mm"
include "3eqtrri.mm"

theorem df2nd2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- { <. <. x , y >. , z >. | z = y } = ( 2nd |` ( _V X. _V ) )

  proof
    c2nd
    cvv
    cvv
    cxp
    #
    cres
    vz
    cv
    #
    vw
    cv
    #
    c2nd
    cfv
    #
    wceq
    #
    vw
    vz
    copab
    #
    @0
    cres
    @2
    @0
    wcel
    @4
    wa
    vw
    vz
    copab
    @1
    vy
    cv
    #
    wceq
    #
    vx
    vy
    vz
    coprab
    c2nd
    @5
    @0
    c2nd
    vw
    cvv
    @3
    cmpt
    #
    @5
    c2nd
    cvv
    wfn
    #
    c2nd
    @8
    wceq
    cvv
    cvv
    c2nd
    wfo
    @9
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    ax-mp
    vw
    cvv
    c2nd
    dffn5
    mpbi
    vw
    vz
    @3
    mptv
    eqtri
    reseq1i
    @4
    vw
    vz
    @0
    resopab
    @4
    @7
    vx
    vy
    vz
    vw
    @2
    vx
    cv
    #
    @6
    cop
    wceq
    @3
    @6
    @1
    @10
    @6
    @2
    vx
    vex
    vy
    vex
    op2ndd
    eqeq2d
    dfoprab3
    3eqtrri
end
