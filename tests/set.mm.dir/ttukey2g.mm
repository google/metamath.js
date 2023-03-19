include "cuni.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wss.mm"
include "wb.mm"
include "wal.mm"
include "wpss.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cdif.mm"
include "wi.mm"
include "difss.mm"
include "ssnum.mm"
include "mpan2.mm"
include "cfv.mm"
include "wf1o.mm"
include "wex.mm"
include "cen.mm"
include "wbr.mm"
include "isnum3.mm"
include "bren.mm"
include "bitri.mm"
include "w3a.mm"
include "cvv.mm"
include "wceq.mm"
include "c0.mm"
include "crn.mm"
include "cif.mm"
include "csn.mm"
include "cun.mm"
include "cmpt.mm"
include "crecs.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "dmeq.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "eqeq1d.mm"
include "rneq.mm"
include "ifbieq2d.mm"
include "id.mm"
include "fveq12d.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "eleq1d.mm"
include "ifbieq1d.mm"
include "ifbieq12d.mm"
include "cbvmptv.mm"
include "recseq.mm"
include "ax-mp.mm"
include "ttukeylem7.mm"
include "3expib.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "syl.mm"
include "3impib.mm"

theorem ttukey2g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B f
  disjoint B w
  disjoint B z
  assert |- ( ( U. A e. dom card /\ B e. A /\ A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) ) -> E. x e. A ( B C_ x /\ A. y e. A -. x C. y ) )

  proof
    cA
    cuni
    #
    ccrd
    cdm
    #
    wcel
    #
    cB
    cA
    wcel
    #
    vx
    cv
    #
    cA
    wcel
    @4
    cpw
    cfn
    cin
    cA
    wss
    wb
    vx
    wal
    #
    cB
    @4
    wss
    @4
    vy
    cv
    wpss
    wn
    vy
    cA
    wral
    wa
    vx
    cA
    wrex
    #
    @2
    @0
    cB
    cdif
    #
    @1
    wcel
    #
    @3
    @5
    wa
    @6
    wi
    #
    @2
    @7
    @0
    wss
    @8
    @0
    cB
    difss
    @0
    @7
    ssnum
    mpan2
    @8
    @7
    ccrd
    cfv
    #
    @7
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @9
    @8
    @10
    @7
    cen
    wbr
    @13
    @7
    isnum3
    @10
    @7
    vf
    bren
    bitri
    @12
    @9
    vf
    @12
    @3
    @5
    @6
    @12
    @3
    @5
    w3a
    vx
    vy
    vz
    cA
    cB
    @11
    vw
    cvv
    vw
    cv
    #
    cdm
    #
    @15
    cuni
    #
    wceq
    #
    @15
    c0
    wceq
    #
    cB
    @14
    crn
    #
    cuni
    #
    cif
    #
    @16
    @14
    cfv
    #
    @22
    @16
    @11
    cfv
    #
    csn
    #
    cun
    #
    cA
    wcel
    #
    @24
    c0
    cif
    #
    cun
    #
    cif
    #
    cmpt
    #
    crecs
    #
    @12
    @3
    @5
    simp1
    @12
    @3
    @5
    simp2
    @12
    @3
    @5
    simp3
    @30
    vz
    cvv
    vz
    cv
    #
    cdm
    #
    @33
    cuni
    #
    wceq
    #
    @33
    c0
    wceq
    #
    cB
    @32
    crn
    #
    cuni
    #
    cif
    #
    @34
    @32
    cfv
    #
    @40
    @34
    @11
    cfv
    #
    csn
    #
    cun
    #
    cA
    wcel
    #
    @42
    c0
    cif
    #
    cun
    #
    cif
    #
    cmpt
    #
    wceq
    @31
    @48
    crecs
    wceq
    vw
    vz
    cvv
    @29
    @47
    @14
    @32
    wceq
    #
    @17
    @35
    @21
    @28
    @39
    @46
    @49
    @15
    @33
    @16
    @34
    @14
    @32
    dmeq
    #
    @49
    @15
    @33
    @50
    unieqd
    #
    eqeq12d
    @49
    @18
    @36
    @20
    @38
    cB
    @49
    @15
    @33
    c0
    @50
    eqeq1d
    @49
    @19
    @37
    @14
    @32
    rneq
    unieqd
    ifbieq2d
    @49
    @22
    @40
    @27
    @45
    @49
    @16
    @34
    @14
    @32
    @49
    id
    @51
    fveq12d
    #
    @49
    @26
    @44
    @24
    @42
    c0
    @49
    @25
    @43
    cA
    @49
    @22
    @40
    @24
    @42
    @52
    @49
    @23
    @41
    @49
    @16
    @34
    @11
    @51
    fveq2d
    sneqd
    #
    uneq12d
    eleq1d
    @53
    ifbieq1d
    uneq12d
    ifbieq12d
    cbvmptv
    @30
    @48
    recseq
    ax-mp
    ttukeylem7
    3expib
    exlimiv
    sylbi
    syl
    3impib
end
