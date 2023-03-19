include "chil.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "cmul.mm"
include "mulcl.mm"
include "ancoms.mm"
include "adantll.mm"
include "ax-hvmulass.mm"
include "3com13.mm"
include "3expa.mm"
include "eqeq2d.mm"
include "biimprd.mm"
include "oveq1.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "3adant3.mm"
include "cdiv.mm"
include "divcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "simprl.mm"
include "simplr.mm"
include "syl3anc.mm"
include "divcan1.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "exp43.mm"
include "com4l.mm"
include "3imp.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "wb.mm"
include "hvmulcl.mm"
include "elspansn.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem spansncol
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. ~H /\ B e. CC /\ B =/= 0 ) -> ( span ` { ( B .h A ) } ) = ( span ` { A } ) )

  proof
    cA
    chil
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    vx
    cB
    cA
    csm
    co
    #
    csn
    cspn
    cfv
    #
    cA
    csn
    cspn
    cfv
    #
    @3
    vx
    cv
    #
    vy
    cv
    #
    @4
    csm
    co
    #
    wceq
    #
    vy
    cc
    wrex
    #
    @7
    vz
    cv
    #
    cA
    csm
    co
    #
    wceq
    #
    vz
    cc
    wrex
    #
    @7
    @5
    wcel
    #
    @7
    @6
    wcel
    #
    @3
    @11
    @15
    @0
    @1
    @11
    @15
    wi
    @2
    @0
    @1
    wa
    #
    @10
    @15
    vy
    cc
    @18
    @8
    cc
    wcel
    #
    wa
    #
    @8
    cB
    cmul
    co
    #
    cc
    wcel
    #
    @10
    @7
    @21
    cA
    csm
    co
    #
    wceq
    #
    @15
    @1
    @19
    @22
    @0
    @19
    @1
    @22
    @8
    cB
    mulcl
    ancoms
    adantll
    @20
    @24
    @10
    @20
    @23
    @9
    @7
    @0
    @1
    @19
    @23
    @9
    wceq
    #
    @19
    @1
    @0
    @25
    @8
    cB
    cA
    ax-hvmulass
    3com13
    3expa
    eqeq2d
    biimprd
    @14
    @24
    vz
    @21
    cc
    @12
    @21
    wceq
    @13
    @23
    @7
    @12
    @21
    cA
    csm
    oveq1
    eqeq2d
    rspcev
    syl6an
    rexlimdva
    3adant3
    @3
    @14
    @11
    vz
    cc
    @0
    @1
    @2
    @12
    cc
    wcel
    #
    @14
    @11
    wi
    #
    wi
    @26
    @0
    @1
    @2
    @27
    @26
    @0
    @1
    @2
    @27
    @26
    @0
    wa
    #
    @1
    @2
    wa
    #
    wa
    #
    @12
    cB
    cdiv
    co
    #
    cc
    wcel
    #
    @14
    @7
    @31
    @4
    csm
    co
    #
    wceq
    #
    @11
    @26
    @29
    @32
    @0
    @26
    @1
    @2
    @32
    @12
    cB
    divcl
    3expb
    adantlr
    #
    @30
    @34
    @14
    @30
    @33
    @13
    @7
    @30
    @31
    cB
    cmul
    co
    #
    cA
    csm
    co
    #
    @33
    @13
    @30
    @32
    @1
    @0
    @37
    @33
    wceq
    @35
    @28
    @1
    @2
    simprl
    @26
    @0
    @29
    simplr
    @31
    cB
    cA
    ax-hvmulass
    syl3anc
    @30
    @36
    @12
    cA
    csm
    @26
    @29
    @36
    @12
    wceq
    #
    @0
    @26
    @1
    @2
    @38
    @12
    cB
    divcan1
    3expb
    adantlr
    oveq1d
    eqtr3d
    eqeq2d
    biimprd
    @10
    @34
    vy
    @31
    cc
    @8
    @31
    wceq
    @9
    @33
    @7
    @8
    @31
    @4
    csm
    oveq1
    eqeq2d
    rspcev
    syl6an
    exp43
    com4l
    3imp
    rexlimdv
    impbid
    @0
    @1
    @16
    @11
    wb
    #
    @2
    @18
    @4
    chil
    wcel
    #
    @39
    @1
    @0
    @40
    cB
    cA
    hvmulcl
    ancoms
    vy
    @4
    @7
    elspansn
    syl
    3adant3
    @0
    @1
    @17
    @15
    wb
    @2
    vz
    cA
    @7
    elspansn
    3ad2ant1
    3bitr4d
    eqrdv
end
