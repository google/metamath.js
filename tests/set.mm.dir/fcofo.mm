include "wf.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "simp1.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrn.mm"
include "3ad2antl2.mm"
include "simpl3.mm"
include "fveq1d.mm"
include "fvco3.mm"
include "fvresi.mm"
include "adantl.mm"
include "3eqtr3rd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem fcofo
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : A --> B /\ S : B --> A /\ ( F o. S ) = ( _I |` B ) ) -> F : A -onto-> B )

  proof
    cA
    cB
    cF
    wf
    #
    cB
    cA
    cS
    wf
    #
    cF
    cS
    ccom
    #
    cid
    cB
    cres
    #
    wceq
    #
    w3a
    #
    @0
    vy
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    cA
    cB
    cF
    wfo
    @0
    @1
    @4
    simp1
    @5
    @10
    vy
    cB
    @5
    @6
    cB
    wcel
    #
    wa
    #
    @6
    cS
    cfv
    #
    cA
    wcel
    #
    @6
    @13
    cF
    cfv
    #
    wceq
    #
    @10
    @1
    @0
    @11
    @14
    @4
    cB
    cA
    @6
    cS
    ffvelrn
    3ad2antl2
    @12
    @6
    @2
    cfv
    #
    @6
    @3
    cfv
    #
    @15
    @6
    @12
    @6
    @2
    @3
    @0
    @1
    @4
    @11
    simpl3
    fveq1d
    @1
    @0
    @11
    @17
    @15
    wceq
    @4
    cB
    cA
    @6
    cF
    cS
    fvco3
    3ad2antl2
    @11
    @18
    @6
    wceq
    @5
    cB
    @6
    fvresi
    adantl
    3eqtr3rd
    @9
    @16
    vx
    @13
    cA
    @7
    @13
    wceq
    @8
    @15
    @6
    @7
    @13
    cF
    fveq2
    eqeq2d
    rspcev
    syl2anc
    ralrimiva
    vx
    vy
    cA
    cB
    cF
    dffo3
    sylanbrc
end
