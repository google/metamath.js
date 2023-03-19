include "cnp.mm"
include "wcel.mm"
include "cvv.mm"
include "c0.mm"
include "wpss.mm"
include "cnq.mm"
include "wa.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wral.mm"
include "elex.mm"
include "wss.mm"
include "pssss.mm"
include "nqex.mm"
include "ssex.mm"
include "syl.mm"
include "ad2antlr.mm"
include "wceq.mm"
include "psseq2.mm"
include "psseq1.mm"
include "anbi12d.mm"
include "eleq2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "rexeq.mm"
include "raleqbi1dv.mm"
include "df-np.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem elnp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( A e. P. <-> ( ( (/) C. A /\ A C. Q. ) /\ A. x e. A ( A. y ( y <Q x -> y e. A ) /\ E. y e. A x <Q y ) ) )

  proof
    cA
    cnp
    wcel
    cA
    cvv
    wcel
    #
    c0
    cA
    wpss
    #
    cA
    cnq
    wpss
    #
    wa
    #
    vy
    cv
    #
    vx
    cv
    #
    cltq
    wbr
    #
    @4
    cA
    wcel
    #
    wi
    #
    vy
    wal
    #
    @5
    @4
    cltq
    wbr
    #
    vy
    cA
    wrex
    #
    wa
    #
    vx
    cA
    wral
    #
    wa
    #
    cA
    cnp
    elex
    @2
    @0
    @1
    @13
    @2
    cA
    cnq
    wss
    @0
    cA
    cnq
    pssss
    cA
    cnq
    nqex
    ssex
    syl
    ad2antlr
    c0
    vz
    cv
    #
    wpss
    #
    @15
    cnq
    wpss
    #
    wa
    #
    @6
    @4
    @15
    wcel
    #
    wi
    #
    vy
    wal
    #
    @10
    vy
    @15
    wrex
    #
    wa
    #
    vx
    @15
    wral
    #
    wa
    @14
    vz
    cA
    cnp
    cvv
    @15
    cA
    wceq
    #
    @18
    @3
    @24
    @13
    @25
    @16
    @1
    @17
    @2
    @15
    cA
    c0
    psseq2
    @15
    cA
    cnq
    psseq1
    anbi12d
    @23
    @12
    vx
    @15
    cA
    @25
    @21
    @9
    @22
    @11
    @25
    @20
    @8
    vy
    @25
    @19
    @7
    @6
    @15
    cA
    @4
    eleq2
    imbi2d
    albidv
    @10
    vy
    @15
    cA
    rexeq
    anbi12d
    raleqbi1dv
    anbi12d
    vz
    vx
    vy
    df-np
    elab2g
    pm5.21nii
end
