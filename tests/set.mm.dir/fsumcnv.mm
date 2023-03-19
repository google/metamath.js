include "csu.mm"
include "ccnv.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "csb.mm"
include "csn.mm"
include "cuni.mm"
include "cmpt.mm"
include "cop.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "fvex.mm"
include "wa.mm"
include "opex.mm"
include "csbie.mm"
include "opeq12.mm"
include "csbeq1d.mm"
include "syl5eqr.mm"
include "csbie2.mm"
include "syl6eqr.mm"
include "cfn.mm"
include "wcel.mm"
include "cnvfi.mm"
include "syl.mm"
include "wf1o.mm"
include "wrel.mm"
include "relcnv.mm"
include "cnvf1o.mm"
include "ax-mp.mm"
include "wb.mm"
include "dfrel2.mm"
include "sylib.mm"
include "f1oeq3.mm"
include "mpbii.mm"
include "1st2nd.mm"
include "mpan.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeltrrd.mm"
include "sneq.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "opswap.mm"
include "syl6eq.mm"
include "eqid.mm"
include "fvmpt.mm"
include "eqtrd.mm"
include "adantl.mm"
include "fsumf1o.mm"
include "ancoms.mm"
include "sumeq2i.mm"

theorem fsumcnv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  assume fsumcnv.1: |- ( x = <. j , k >. -> B = D )
  assume fsumcnv.2: |- ( y = <. k , j >. -> C = D )
  assume fsumcnv.3: |- ( ph -> A e. Fin )
  assume fsumcnv.4: |- ( ph -> Rel A )
  assume fsumcnv.5: |- ( ( ph /\ x e. A ) -> B e. CC )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint j k
  disjoint j y
  disjoint B j
  disjoint k y
  disjoint B k
  disjoint B y
  disjoint j x
  disjoint C j
  disjoint k x
  disjoint C k
  disjoint C x
  disjoint ph x
  disjoint ph y
  disjoint D x
  disjoint D y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint ph z
  assert |- ( ph -> sum_ x e. A B = sum_ y e. `' A C )

  proof
    wph
    cA
    cB
    vx
    csu
    cA
    ccnv
    #
    vj
    vy
    cv
    #
    c2nd
    cfv
    #
    vk
    @1
    c1st
    cfv
    #
    cD
    csb
    csb
    #
    vy
    csu
    @0
    cC
    vy
    csu
    wph
    cA
    cB
    @0
    @4
    vx
    vy
    vz
    @0
    vz
    cv
    #
    csn
    #
    ccnv
    #
    cuni
    #
    cmpt
    #
    @2
    @3
    cop
    #
    vx
    cv
    @10
    wceq
    cB
    vx
    @10
    cB
    csb
    #
    @4
    vx
    @10
    cB
    csbeq1a
    vj
    vk
    @2
    @3
    cD
    @11
    @1
    c2nd
    fvex
    #
    @1
    c1st
    fvex
    #
    vj
    cv
    #
    @2
    wceq
    #
    vk
    cv
    #
    @3
    wceq
    #
    wa
    #
    cD
    vx
    @14
    @16
    cop
    #
    cB
    csb
    @11
    vx
    @19
    cB
    cD
    @14
    @16
    opex
    fsumcnv.1
    csbie
    @18
    vx
    @19
    @10
    cB
    @14
    @16
    @2
    @3
    opeq12
    csbeq1d
    syl5eqr
    csbie2
    syl6eqr
    wph
    cA
    cfn
    wcel
    @0
    cfn
    wcel
    fsumcnv.3
    cA
    cnvfi
    syl
    wph
    @0
    @0
    ccnv
    #
    @9
    wf1o
    #
    @0
    cA
    @9
    wf1o
    #
    @0
    wrel
    #
    @21
    cA
    relcnv
    #
    vz
    @0
    cnvf1o
    ax-mp
    wph
    @20
    cA
    wceq
    #
    @21
    @22
    wb
    wph
    cA
    wrel
    @25
    fsumcnv.4
    cA
    dfrel2
    sylib
    @20
    cA
    @0
    @9
    f1oeq3
    syl
    mpbii
    @1
    @0
    wcel
    #
    @1
    @9
    cfv
    #
    @10
    wceq
    wph
    @26
    @27
    @3
    @2
    cop
    #
    @9
    cfv
    #
    @10
    @26
    @1
    @28
    @9
    @23
    @26
    @1
    @28
    wceq
    #
    @24
    @1
    @0
    1st2nd
    mpan
    #
    fveq2d
    @26
    @28
    @0
    wcel
    @29
    @10
    wceq
    @26
    @1
    @28
    @0
    @31
    @26
    id
    eqeltrrd
    vz
    @28
    @8
    @10
    @0
    @9
    @5
    @28
    wceq
    #
    @8
    @28
    csn
    #
    ccnv
    #
    cuni
    @10
    @32
    @7
    @34
    @32
    @6
    @33
    @5
    @28
    sneq
    cnveqd
    unieqd
    @3
    @2
    opswap
    syl6eq
    @9
    eqid
    @2
    @3
    opex
    fvmpt
    syl
    eqtrd
    adantl
    fsumcnv.5
    fsumf1o
    @0
    cC
    @4
    vy
    @26
    cC
    vy
    @28
    cC
    csb
    #
    @4
    @26
    @30
    cC
    @35
    wceq
    @31
    vy
    @28
    cC
    csbeq1a
    syl
    vj
    vk
    @2
    @3
    cD
    @35
    @12
    @13
    @18
    cD
    vy
    @16
    @14
    cop
    #
    cC
    csb
    @35
    vy
    @36
    cC
    cD
    @16
    @14
    opex
    fsumcnv.2
    csbie
    @18
    vy
    @36
    @28
    cC
    @17
    @15
    @36
    @28
    wceq
    @16
    @14
    @3
    @2
    opeq12
    ancoms
    csbeq1d
    syl5eqr
    csbie2
    syl6eqr
    sumeq2i
    syl6eqr
end
