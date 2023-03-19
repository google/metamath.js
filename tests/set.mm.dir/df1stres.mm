include "c1st.mm"
include "cxp.mm"
include "cres.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "cmpt2.mm"
include "cvv.mm"
include "df1st2.mm"
include "reseq1i.mm"
include "resoprab.mm"
include "cin.mm"
include "resres.mm"
include "incom.mm"
include "wss.mm"
include "xpss.mm"
include "df-ss.mm"
include "mpbi.mm"
include "eqtr3i.mm"
include "reseq2i.mm"
include "eqtri.mm"
include "3eqtr3ri.mm"
include "df-mpt2.mm"
include "eqtr4i.mm"

theorem df1stres
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  assert |- ( 1st |` ( A X. B ) ) = ( x e. A , y e. B |-> x )

  proof
    c1st
    cA
    cB
    cxp
    #
    cres
    #
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    vz
    cv
    @2
    wceq
    #
    wa
    vx
    vy
    vz
    coprab
    #
    vx
    vy
    cA
    cB
    @2
    cmpt2
    @3
    vx
    vy
    vz
    coprab
    #
    @0
    cres
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    @0
    cres
    #
    @4
    @1
    @5
    @7
    @0
    vx
    vy
    vz
    df1st2
    reseq1i
    @3
    vx
    vy
    vz
    cA
    cB
    resoprab
    @8
    c1st
    @6
    @0
    cin
    #
    cres
    @1
    c1st
    @6
    @0
    resres
    @9
    @0
    c1st
    @0
    @6
    cin
    #
    @9
    @0
    @0
    @6
    incom
    @0
    @6
    wss
    @10
    @0
    wceq
    cA
    cB
    xpss
    @0
    @6
    df-ss
    mpbi
    eqtr3i
    reseq2i
    eqtri
    3eqtr3ri
    vx
    vy
    vz
    cA
    cB
    @2
    df-mpt2
    eqtr4i
end
