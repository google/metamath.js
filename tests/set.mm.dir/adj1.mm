include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "chil.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "cop.mm"
include "w3a.mm"
include "copab.mm"
include "wfun.mm"
include "funadj.mm"
include "funfvop.mm"
include "mpan.mm"
include "dfadj2.mm"
include "syl6eleq.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "3anbi13d.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "3anbi23d.mm"
include "opelopabg.mm"
include "mpan2.mm"
include "mpbid.mm"
include "simp3d.mm"
include "oveq1.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem adj1
  let cA: class A
  let cB: class B
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S


  assert |- ( ( T e. dom adjh /\ A e. ~H /\ B e. ~H ) -> ( A .ih ( T ` B ) ) = ( ( ( adjh ` T ) ` A ) .ih B ) )

  proof
    cT
    cado
    cdm
    #
    wcel
    #
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cB
    cT
    cfv
    #
    csp
    co
    #
    cA
    cT
    cado
    cfv
    #
    cfv
    #
    cB
    csp
    co
    #
    wceq
    #
    @1
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    #
    csp
    co
    #
    @10
    @6
    cfv
    #
    @11
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    @2
    @3
    wa
    @9
    @1
    chil
    chil
    cT
    wf
    #
    chil
    chil
    @6
    wf
    #
    @17
    @1
    cT
    @6
    cop
    #
    chil
    chil
    vz
    cv
    #
    wf
    #
    chil
    chil
    vw
    cv
    #
    wf
    #
    @10
    @11
    @21
    cfv
    #
    csp
    co
    #
    @10
    @23
    cfv
    #
    @11
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    #
    vz
    vw
    copab
    #
    wcel
    #
    @18
    @19
    @17
    w3a
    #
    @1
    @20
    cado
    @32
    cado
    wfun
    @1
    @20
    cado
    wcel
    funadj
    cT
    cado
    funfvop
    mpan
    vx
    vy
    vw
    vz
    dfadj2
    syl6eleq
    @1
    @6
    cvv
    wcel
    @33
    @34
    wb
    cT
    cado
    fvex
    @31
    @18
    @24
    @13
    @28
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    @34
    vz
    vw
    cT
    @6
    @0
    cvv
    @21
    cT
    wceq
    #
    @22
    @18
    @30
    @36
    @24
    chil
    chil
    @21
    cT
    feq1
    @37
    @29
    @35
    vx
    vy
    chil
    chil
    @37
    @26
    @13
    @28
    @37
    @25
    @12
    @10
    csp
    @11
    @21
    cT
    fveq1
    oveq2d
    eqeq1d
    2ralbidv
    3anbi13d
    @23
    @6
    wceq
    #
    @24
    @19
    @36
    @17
    @18
    chil
    chil
    @23
    @6
    feq1
    @38
    @35
    @16
    vx
    vy
    chil
    chil
    @38
    @28
    @15
    @13
    @38
    @27
    @14
    @11
    csp
    @10
    @23
    @6
    fveq1
    oveq1d
    eqeq2d
    2ralbidv
    3anbi23d
    opelopabg
    mpan2
    mpbid
    simp3d
    @16
    @9
    cA
    @12
    csp
    co
    #
    @7
    @11
    csp
    co
    #
    wceq
    vx
    vy
    cA
    cB
    chil
    chil
    @10
    cA
    wceq
    #
    @13
    @39
    @15
    @40
    @10
    cA
    @12
    csp
    oveq1
    @41
    @14
    @7
    @11
    csp
    @10
    cA
    @6
    fveq2
    oveq1d
    eqeq12d
    @11
    cB
    wceq
    #
    @39
    @5
    @40
    @8
    @42
    @12
    @4
    cA
    csp
    @11
    cB
    cT
    fveq2
    oveq2d
    @11
    cB
    @7
    csp
    oveq2
    eqeq12d
    rspc2v
    syl5com
    3impib
end
