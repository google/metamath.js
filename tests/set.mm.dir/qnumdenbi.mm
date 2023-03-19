include "cq.mm"
include "wcel.mm"
include "cz.mm"
include "cn.mm"
include "w3a.mm"
include "cnumer.mm"
include "cfv.mm"
include "wceq.mm"
include "cdenom.mm"
include "wa.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "cxp.mm"
include "crio.mm"
include "cop.mm"
include "wb.mm"
include "wreu.mm"
include "qredeu.mm"
include "riotacl.mm"
include "1st2nd2.mm"
include "3syl.mm"
include "qnumval.mm"
include "qdenval.mm"
include "opeq12d.mm"
include "eqtr4d.mm"
include "eqeq1d.mm"
include "3ad2ant1.mm"
include "fvex.mm"
include "opth.mm"
include "syl6rbb.mm"
include "opelxpi.mm"
include "3adant1.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "op1stg.mm"
include "op2ndg.mm"
include "3bitr2rd.mm"

theorem qnumdenbi
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vx: setvar x


  assert |- ( ( A e. QQ /\ B e. ZZ /\ C e. NN ) -> ( ( ( B gcd C ) = 1 /\ A = ( B / C ) ) <-> ( ( numer ` A ) = B /\ ( denom ` A ) = C ) ) )

  proof
    cA
    cq
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cA
    cnumer
    cfv
    #
    cB
    wceq
    cA
    cdenom
    cfv
    #
    cC
    wceq
    wa
    #
    va
    cv
    #
    c1st
    cfv
    #
    @7
    c2nd
    cfv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    @8
    @9
    cdiv
    co
    #
    wceq
    #
    wa
    #
    va
    cz
    cn
    cxp
    #
    crio
    #
    cB
    cC
    cop
    #
    wceq
    #
    @17
    c1st
    cfv
    #
    @17
    c2nd
    cfv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    @19
    @20
    cdiv
    co
    #
    wceq
    #
    wa
    #
    cB
    cC
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    cB
    cC
    cdiv
    co
    #
    wceq
    #
    wa
    @3
    @18
    @4
    @5
    cop
    #
    @17
    wceq
    #
    @6
    @0
    @1
    @18
    @31
    wb
    @2
    @0
    @16
    @30
    @17
    @0
    @16
    @16
    c1st
    cfv
    #
    @16
    c2nd
    cfv
    #
    cop
    #
    @30
    @0
    @14
    va
    @15
    wreu
    #
    @16
    @15
    wcel
    @16
    @34
    wceq
    va
    cA
    qredeu
    #
    @14
    va
    @15
    riotacl
    @16
    cz
    cn
    1st2nd2
    3syl
    @0
    @4
    @32
    @5
    @33
    va
    cA
    qnumval
    va
    cA
    qdenval
    opeq12d
    eqtr4d
    eqeq1d
    3ad2ant1
    @4
    @5
    cB
    cC
    cA
    cnumer
    fvex
    cA
    cdenom
    fvex
    opth
    syl6rbb
    @3
    @17
    @15
    wcel
    #
    @35
    @25
    @18
    wb
    @1
    @2
    @37
    @0
    cB
    cC
    cz
    cn
    opelxpi
    3adant1
    @0
    @1
    @35
    @2
    @36
    3ad2ant1
    @14
    @25
    va
    @15
    @17
    @7
    @17
    wceq
    #
    @11
    @22
    @13
    @24
    @38
    @10
    @21
    c1
    @38
    @8
    @19
    @9
    @20
    cgcd
    @7
    @17
    c1st
    fveq2
    #
    @7
    @17
    c2nd
    fveq2
    #
    oveq12d
    eqeq1d
    @38
    @12
    @23
    cA
    @38
    @8
    @19
    @9
    @20
    cdiv
    @39
    @40
    oveq12d
    eqeq2d
    anbi12d
    riota2
    syl2anc
    @3
    @22
    @27
    @24
    @29
    @3
    @21
    @26
    c1
    @1
    @2
    @21
    @26
    wceq
    @0
    @1
    @2
    wa
    @19
    cB
    @20
    cC
    cgcd
    cB
    cC
    cz
    cn
    op1stg
    #
    cB
    cC
    cz
    cn
    op2ndg
    #
    oveq12d
    3adant1
    eqeq1d
    @3
    @23
    @28
    cA
    @3
    @19
    cB
    @20
    cC
    cdiv
    @1
    @2
    @19
    cB
    wceq
    @0
    @41
    3adant1
    @1
    @2
    @20
    cC
    wceq
    @0
    @42
    3adant1
    oveq12d
    eqeq2d
    anbi12d
    3bitr2rd
end
