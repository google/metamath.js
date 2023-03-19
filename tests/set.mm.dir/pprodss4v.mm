include "cpprod.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccom.mm"
include "c2nd.mm"
include "ctxp.mm"
include "df-pprod.mm"
include "txprel.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "txpss3v.mm"
include "sseli.mm"
include "opelxp2.mm"
include "syl.mm"
include "wceq.mm"
include "wex.mm"
include "wi.mm"
include "elvv.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "wbr.mm"
include "df-br.mm"
include "wa.mm"
include "vex.mm"
include "brtxp.mm"
include "brco.mm"
include "brres.mm"
include "simprbi.mm"
include "adantr.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "sylbir.mm"
include "syl6bi.mm"
include "exlimivv.mm"
include "mpcom.mm"
include "opelxp.mm"
include "sylanbrc.mm"
include "relssi.mm"
include "eqsstri.mm"

theorem pprodss4v
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- pprod ( A , B ) C_ ( ( _V X. _V ) X. ( _V X. _V ) )

  proof
    cA
    cB
    cpprod
    cA
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    ccom
    #
    cB
    c2nd
    @0
    cres
    ccom
    #
    ctxp
    #
    @0
    @0
    cxp
    #
    cA
    cB
    df-pprod
    vx
    vy
    @4
    @5
    @2
    @3
    txprel
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @4
    wcel
    #
    @6
    @0
    wcel
    #
    @7
    @0
    wcel
    #
    @8
    @5
    wcel
    @11
    @9
    @10
    @9
    @8
    cvv
    @0
    cxp
    #
    wcel
    @11
    @4
    @12
    @8
    @2
    @3
    txpss3v
    sseli
    @6
    @7
    cvv
    @0
    opelxp2
    syl
    #
    @11
    @7
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    wceq
    #
    vw
    wex
    vz
    wex
    @9
    @10
    wi
    #
    vz
    vw
    @7
    elvv
    @17
    @18
    vz
    vw
    @17
    @9
    @6
    @16
    cop
    #
    @4
    wcel
    #
    @10
    @17
    @8
    @19
    @4
    @7
    @16
    @6
    opeq2
    eleq1d
    @20
    @6
    @16
    @4
    wbr
    #
    @10
    @6
    @16
    @4
    df-br
    @21
    @6
    @14
    @2
    wbr
    #
    @6
    @15
    @3
    wbr
    #
    wa
    @10
    @2
    @3
    @6
    @14
    @15
    vx
    vex
    #
    vz
    vex
    #
    vw
    vex
    brtxp
    @22
    @10
    @23
    @22
    @6
    @7
    @1
    wbr
    #
    @7
    @14
    cA
    wbr
    #
    wa
    #
    vy
    wex
    @10
    vy
    @6
    @14
    cA
    @1
    @24
    @25
    brco
    @28
    @10
    vy
    @26
    @10
    @27
    @26
    @6
    @7
    c1st
    wbr
    @10
    @6
    @7
    c1st
    @0
    vy
    vex
    brres
    simprbi
    adantr
    exlimiv
    sylbi
    adantr
    sylbi
    sylbir
    syl6bi
    exlimivv
    sylbi
    mpcom
    @13
    @6
    @7
    @0
    @0
    opelxp
    sylanbrc
    relssi
    eqsstri
end
