include "ctop.mm"
include "wcel.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "ciin.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cint.mm"
include "simpr3.mm"
include "dfiin2g.mm"
include "syl.mm"
include "wss.mm"
include "simpl.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "rnmpt.mm"
include "wf.mm"
include "fmpt.mm"
include "sylib.mm"
include "frn.mm"
include "syl5eqssr.mm"
include "cdm.mm"
include "fdm.mm"
include "simpr2.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "eqeq1i.mm"
include "bitri.mm"
include "necon3bii.mm"
include "simpr1.mm"
include "abrexfi.mm"
include "fiinopn.mm"
include "imp.mm"
include "syl13anc.mm"
include "eqeltrd.mm"

theorem iinopn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let vy: setvar y

  disjoint A x
  disjoint J x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint J y
  assert |- ( ( J e. Top /\ ( A e. Fin /\ A =/= (/) /\ A. x e. A B e. J ) ) -> |^|_ x e. A B e. J )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    cB
    cJ
    wcel
    vx
    cA
    wral
    #
    w3a
    #
    wa
    #
    vx
    cA
    cB
    ciin
    #
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cint
    #
    cJ
    @5
    @3
    @6
    @8
    wceq
    @0
    @1
    @2
    @3
    simpr3
    #
    vx
    vy
    cA
    cB
    cJ
    dfiin2g
    syl
    @5
    @0
    @7
    cJ
    wss
    #
    @7
    c0
    wne
    #
    @7
    cfn
    wcel
    #
    @8
    cJ
    wcel
    #
    @0
    @4
    simpl
    @5
    @7
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cJ
    vx
    vy
    cA
    cB
    @14
    @14
    eqid
    #
    rnmpt
    #
    @5
    cA
    cJ
    @14
    wf
    #
    @15
    cJ
    wss
    @5
    @3
    @18
    @9
    vx
    cA
    cJ
    cB
    @14
    @16
    fmpt
    sylib
    #
    cA
    cJ
    @14
    frn
    syl
    syl5eqssr
    @5
    @14
    cdm
    #
    c0
    wne
    @11
    @5
    @20
    cA
    c0
    @5
    @18
    @20
    cA
    wceq
    @19
    cA
    cJ
    @14
    fdm
    syl
    @0
    @1
    @2
    @3
    simpr2
    eqnetrd
    @20
    c0
    @7
    c0
    @20
    c0
    wceq
    @15
    c0
    wceq
    @7
    c0
    wceq
    @14
    dm0rn0
    @15
    @7
    c0
    @17
    eqeq1i
    bitri
    necon3bii
    sylib
    @5
    @1
    @12
    @0
    @1
    @2
    @3
    simpr1
    vx
    vy
    cA
    cB
    abrexfi
    syl
    @0
    @10
    @11
    @12
    w3a
    @13
    @7
    cJ
    fiinopn
    imp
    syl13anc
    eqeltrd
end
