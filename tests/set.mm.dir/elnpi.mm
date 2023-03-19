include "cnp.mm"
include "wcel.mm"
include "cvv.mm"
include "c0.mm"
include "wpss.mm"
include "cnq.mm"
include "w3a.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "elex.mm"
include "simpl1.mm"
include "wel.mm"
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
include "id.mm"
include "3expib.mm"
include "3simpc.mm"
include "impbid1.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "pm5.21nii.mm"

theorem elnpi
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
  assert |- ( A e. P. <-> ( ( A e. _V /\ (/) C. A /\ A C. Q. ) /\ A. x e. A ( A. y ( y <Q x -> y e. A ) /\ E. y e. A x <Q y ) ) )

  proof
    cA
    cnp
    wcel
    #
    cA
    cvv
    wcel
    #
    @1
    c0
    cA
    wpss
    #
    cA
    cnq
    wpss
    #
    w3a
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
    @5
    cA
    wcel
    #
    wi
    #
    vy
    wal
    #
    @6
    @5
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
    @1
    @2
    @3
    @14
    simpl1
    @1
    @0
    @2
    @3
    wa
    #
    @14
    wa
    #
    @15
    c0
    vz
    cv
    #
    wpss
    #
    @18
    cnq
    wpss
    #
    wa
    #
    @7
    vy
    vz
    wel
    #
    wi
    #
    vy
    wal
    #
    @11
    vy
    @18
    wrex
    #
    wa
    #
    vx
    @18
    wral
    #
    wa
    @17
    vz
    cA
    cnp
    cvv
    @18
    cA
    wceq
    #
    @21
    @16
    @27
    @14
    @28
    @19
    @2
    @20
    @3
    @18
    cA
    c0
    psseq2
    @18
    cA
    cnq
    psseq1
    anbi12d
    @26
    @13
    vx
    @18
    cA
    @28
    @24
    @10
    @25
    @12
    @28
    @23
    @9
    vy
    @28
    @22
    @8
    @7
    @18
    cA
    @5
    eleq2
    imbi2d
    albidv
    @11
    vy
    @18
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
    @1
    @16
    @4
    @14
    @1
    @16
    @4
    @1
    @2
    @3
    @4
    @4
    id
    3expib
    @1
    @2
    @3
    3simpc
    impbid1
    anbi1d
    bitrd
    pm5.21nii
end
