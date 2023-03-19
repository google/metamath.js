include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "csb.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "cpr.mm"
include "wral.mm"
include "wa.mm"
include "wdisj.mm"
include "wb.mm"
include "eqeq1.mm"
include "nfcv.mm"
include "csbhypf.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "ralbidv.mm"
include "ralprg.mm"
include "3adant3.mm"
include "wtru.mm"
include "id.mm"
include "eqcomd.mm"
include "orcd.mm"
include "a1tru.mm"
include "2thd.mm"
include "eqeq2.mm"
include "ineq2d.mm"
include "wn.mm"
include "simp3.mm"
include "neneqd.mm"
include "biorf.mm"
include "syl.mm"
include "tru.mm"
include "biantrur.mm"
include "syl6bb.mm"
include "bitr4d.mm"
include "eqcom.mm"
include "incom.mm"
include "syl6eq.mm"
include "biantru.mm"
include "anbi12d.mm"
include "bitrd.mm"
include "disjors.mm"
include "pm4.24.mm"
include "3bitr4g.mm"

theorem disjprg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  assume disjprg.1: |- ( x = A -> C = D )
  assume disjprg.2: |- ( x = B -> C = E )

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint E x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint D y
  disjoint D z
  disjoint E y
  disjoint E z
  assert |- ( ( A e. V /\ B e. V /\ A =/= B ) -> ( Disj_ x e. { A , B } C <-> ( D i^i E ) = (/) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    vy
    cv
    #
    vz
    cv
    #
    wceq
    #
    vx
    @4
    cC
    csb
    #
    vx
    @5
    cC
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vz
    cA
    cB
    cpr
    #
    wral
    #
    vy
    @12
    wral
    #
    cD
    cE
    cin
    #
    c0
    wceq
    #
    @16
    wa
    #
    vx
    @12
    cC
    wdisj
    @16
    @3
    @14
    cA
    @5
    wceq
    #
    cD
    @8
    cin
    #
    c0
    wceq
    #
    wo
    #
    vz
    @12
    wral
    #
    cB
    @5
    wceq
    #
    cE
    @8
    cin
    #
    c0
    wceq
    #
    wo
    #
    vz
    @12
    wral
    #
    wa
    #
    @17
    @0
    @1
    @14
    @28
    wb
    @2
    @13
    @22
    @27
    vy
    cA
    cB
    cV
    cV
    @4
    cA
    wceq
    #
    @11
    @21
    vz
    @12
    @29
    @6
    @18
    @10
    @20
    @4
    cA
    @5
    eqeq1
    @29
    @9
    @19
    c0
    @29
    @7
    cD
    @8
    vx
    vy
    cA
    cC
    cD
    vx
    cA
    nfcv
    #
    vx
    cD
    nfcv
    #
    disjprg.1
    csbhypf
    ineq1d
    eqeq1d
    orbi12d
    ralbidv
    @4
    cB
    wceq
    #
    @11
    @26
    vz
    @12
    @32
    @6
    @23
    @10
    @25
    @4
    cB
    @5
    eqeq1
    @32
    @9
    @24
    c0
    @32
    @7
    cE
    @8
    vx
    vy
    cB
    cC
    cE
    vx
    cB
    nfcv
    #
    vx
    cE
    nfcv
    #
    disjprg.2
    csbhypf
    ineq1d
    eqeq1d
    orbi12d
    ralbidv
    ralprg
    3adant3
    @3
    @22
    @16
    @27
    @16
    @3
    @22
    wtru
    cA
    cB
    wceq
    #
    @16
    wo
    #
    wa
    #
    @16
    @0
    @1
    @22
    @37
    wb
    @2
    @21
    wtru
    @36
    vz
    cA
    cB
    cV
    cV
    @5
    cA
    wceq
    #
    @21
    wtru
    @38
    @18
    @20
    @38
    @5
    cA
    @38
    id
    eqcomd
    orcd
    @38
    a1tru
    2thd
    @5
    cB
    wceq
    #
    @18
    @35
    @20
    @16
    @5
    cB
    cA
    eqeq2
    @39
    @19
    @15
    c0
    @39
    @8
    cE
    cD
    vx
    vz
    cB
    cC
    cE
    @33
    @34
    disjprg.2
    csbhypf
    ineq2d
    eqeq1d
    orbi12d
    ralprg
    3adant3
    @3
    @16
    @36
    @37
    @3
    @35
    wn
    @16
    @36
    wb
    @3
    cA
    cB
    @0
    @1
    @2
    simp3
    neneqd
    @35
    @16
    biorf
    syl
    #
    wtru
    @36
    tru
    biantrur
    syl6bb
    bitr4d
    @3
    @27
    @36
    wtru
    wa
    #
    @16
    @0
    @1
    @27
    @41
    wb
    @2
    @26
    @36
    wtru
    vz
    cA
    cB
    cV
    cV
    @38
    @23
    @35
    @25
    @16
    @38
    @23
    cB
    cA
    wceq
    @35
    @5
    cA
    cB
    eqeq2
    cB
    cA
    eqcom
    syl6bb
    @38
    @24
    @15
    c0
    @38
    @24
    cE
    cD
    cin
    @15
    @38
    @8
    cD
    cE
    vx
    vz
    cA
    cC
    cD
    @30
    @31
    disjprg.1
    csbhypf
    ineq2d
    cE
    cD
    incom
    syl6eq
    eqeq1d
    orbi12d
    @39
    @26
    wtru
    @39
    @23
    @25
    @39
    @5
    cB
    @39
    id
    eqcomd
    orcd
    @39
    a1tru
    2thd
    ralprg
    3adant3
    @3
    @16
    @36
    @41
    @40
    wtru
    @36
    tru
    biantru
    syl6bb
    bitr4d
    anbi12d
    bitrd
    vx
    @12
    cC
    vy
    vz
    disjors
    @16
    pm4.24
    3bitr4g
end
