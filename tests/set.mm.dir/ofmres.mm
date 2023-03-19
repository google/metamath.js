include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cin.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cxp.mm"
include "cres.mm"
include "cof.mm"
include "wss.mm"
include "wceq.mm"
include "ssv.mm"
include "resmpt2.mm"
include "mp2an.mm"
include "df-of.mm"
include "reseq1i.mm"
include "eqid.mm"
include "wcel.mm"
include "vex.mm"
include "dmex.mm"
include "inex1.mm"
include "mptex.mm"
include "ovmpt4g.mm"
include "mp3an.mm"
include "mpt2eq123i.mm"
include "3eqtr4i.mm"

theorem ofmres
  let cA: class A
  let cB: class B
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x

  disjoint f g
  disjoint A f
  disjoint A g
  disjoint B f
  disjoint B g
  disjoint R f
  disjoint R g
  disjoint f x
  disjoint g x
  disjoint R x
  assert |- ( oF R |` ( A X. B ) ) = ( f e. A , g e. B |-> ( f oF R g ) )

  proof
    vf
    vg
    cvv
    cvv
    vx
    vf
    cv
    #
    cdm
    #
    vg
    cv
    #
    cdm
    #
    cin
    #
    vx
    cv
    #
    @0
    cfv
    @5
    @2
    cfv
    cR
    co
    #
    cmpt
    #
    cmpt2
    #
    cA
    cB
    cxp
    #
    cres
    #
    vf
    vg
    cA
    cB
    @7
    cmpt2
    #
    cR
    cof
    #
    @9
    cres
    vf
    vg
    cA
    cB
    @0
    @2
    @12
    co
    #
    cmpt2
    cA
    cvv
    wss
    cB
    cvv
    wss
    @10
    @11
    wceq
    cA
    ssv
    cB
    ssv
    vf
    vg
    cvv
    cvv
    cA
    cB
    @7
    resmpt2
    mp2an
    @12
    @8
    @9
    vx
    cR
    vf
    vg
    df-of
    #
    reseq1i
    vf
    vg
    cA
    cB
    @13
    cA
    cB
    @7
    cA
    eqid
    cB
    eqid
    @0
    cvv
    wcel
    @2
    cvv
    wcel
    @7
    cvv
    wcel
    @13
    @7
    wceq
    vf
    vex
    #
    vg
    vex
    vx
    @4
    @6
    @1
    @3
    @0
    @15
    dmex
    inex1
    mptex
    vf
    vg
    cvv
    cvv
    @7
    @12
    cvv
    @14
    ovmpt4g
    mp3an
    mpt2eq123i
    3eqtr4i
end
