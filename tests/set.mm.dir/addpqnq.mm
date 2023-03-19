include "cnq.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cplq.mm"
include "cfv.mm"
include "cplpq.mm"
include "cerq.mm"
include "co.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "df-plq.mm"
include "fveq1i.mm"
include "a1i.mm"
include "opelxpi.mm"
include "fvres.mm"
include "syl.mm"
include "cnpi.mm"
include "wfn.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmi.mm"
include "cpli.mm"
include "df-plpq.mm"
include "opex.mm"
include "fnmpt2i.mm"
include "elpqn.mm"
include "syl2an.mm"
include "fvco2.mm"
include "sylancr.mm"
include "3eqtrd.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem addpqnq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- ( ( A e. Q. /\ B e. Q. ) -> ( A +Q B ) = ( /Q ` ( A +pQ B ) ) )

  proof
    cA
    cnq
    wcel
    #
    cB
    cnq
    wcel
    #
    wa
    #
    cA
    cB
    cop
    #
    cplq
    cfv
    #
    @3
    cplpq
    cfv
    #
    cerq
    cfv
    #
    cA
    cB
    cplq
    co
    cA
    cB
    cplpq
    co
    #
    cerq
    cfv
    @2
    @4
    @3
    cerq
    cplpq
    ccom
    #
    cnq
    cnq
    cxp
    #
    cres
    #
    cfv
    #
    @3
    @8
    cfv
    #
    @6
    @4
    @11
    wceq
    @2
    @3
    cplq
    @10
    df-plq
    fveq1i
    a1i
    @2
    @3
    @9
    wcel
    @11
    @12
    wceq
    cA
    cB
    cnq
    cnq
    opelxpi
    @3
    @9
    @8
    fvres
    syl
    @2
    cplpq
    cnpi
    cnpi
    cxp
    #
    @13
    cxp
    #
    wfn
    @3
    @14
    wcel
    #
    @12
    @6
    wceq
    vx
    vy
    @13
    @13
    vx
    cv
    #
    c1st
    cfv
    vy
    cv
    #
    c2nd
    cfv
    #
    cmi
    co
    @17
    c1st
    cfv
    @16
    c2nd
    cfv
    #
    cmi
    co
    cpli
    co
    #
    @19
    @18
    cmi
    co
    #
    cop
    cplpq
    vx
    vy
    df-plpq
    @20
    @21
    opex
    fnmpt2i
    @0
    cA
    @13
    wcel
    cB
    @13
    wcel
    @15
    @1
    cA
    elpqn
    cB
    elpqn
    cA
    cB
    @13
    @13
    opelxpi
    syl2an
    @14
    cerq
    cplpq
    @3
    fvco2
    sylancr
    3eqtrd
    cA
    cB
    cplq
    df-ov
    @7
    @5
    cerq
    cA
    cB
    cplpq
    df-ov
    fveq2i
    3eqtr4g
end
