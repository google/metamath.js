include "c1st.mm"
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
include "fo1st.mm"
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
include "op1std.mm"
include "eqeq2d.mm"
include "dfoprab3.mm"
include "3eqtrri.mm"

theorem df1st2
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
  assert |- { <. <. x , y >. , z >. | z = x } = ( 1st |` ( _V X. _V ) )

  proof
    c1st
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
    c1st
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
    vx
    cv
    #
    wceq
    #
    vx
    vy
    vz
    coprab
    c1st
    @5
    @0
    c1st
    vw
    cvv
    @3
    cmpt
    #
    @5
    c1st
    cvv
    wfn
    #
    c1st
    @8
    wceq
    cvv
    cvv
    c1st
    wfo
    @9
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    vw
    cvv
    c1st
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
    @6
    vy
    cv
    #
    cop
    wceq
    @3
    @6
    @1
    @6
    @10
    @2
    vx
    vex
    vy
    vex
    op1std
    eqeq2d
    dfoprab3
    3eqtrri
end
