include "chil.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "ccnfn.mm"
include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "cv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cabs.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "0cn.mm"
include "fconst6.mm"
include "wa.mm"
include "c1.mm"
include "1rp.mm"
include "wceq.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "oveqan12rd.mm"
include "adantlr.mm"
include "0m0e0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "abs0.mm"
include "rpgt0.mm"
include "ad2antlr.mm"
include "eqbrtrd.mm"
include "a1d.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "rgen2.mm"
include "elcnfn.mm"
include "mpbir2an.mm"

theorem 0cnfn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ~H X. { 0 } ) e. ContFn

  proof
    chil
    cc0
    csn
    cxp
    #
    ccnfn
    wcel
    chil
    cc
    @0
    wf
    vw
    cv
    #
    vx
    cv
    #
    cmv
    co
    cno
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @1
    @0
    cfv
    #
    @2
    @0
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    chil
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    chil
    wral
    chil
    cc0
    cc
    0cn
    fconst6
    @14
    vx
    vy
    chil
    crp
    @2
    chil
    wcel
    #
    @10
    crp
    wcel
    #
    wa
    #
    c1
    crp
    wcel
    @3
    c1
    clt
    wbr
    #
    @11
    wi
    #
    vw
    chil
    wral
    #
    @14
    1rp
    @17
    @19
    vw
    chil
    @17
    @1
    chil
    wcel
    #
    wa
    #
    @11
    @18
    @22
    @9
    cc0
    @10
    clt
    @22
    @9
    cc0
    cabs
    cfv
    cc0
    @22
    @8
    cc0
    cabs
    @22
    @8
    cc0
    cc0
    cmin
    co
    #
    cc0
    @15
    @21
    @8
    @23
    wceq
    @16
    @21
    @15
    @6
    cc0
    @7
    cc0
    cmin
    chil
    cc0
    @1
    c0ex
    fvconst2
    chil
    cc0
    @2
    c0ex
    fvconst2
    oveqan12rd
    adantlr
    0m0e0
    syl6eq
    fveq2d
    abs0
    syl6eq
    @16
    cc0
    @10
    clt
    wbr
    @15
    @21
    @10
    rpgt0
    ad2antlr
    eqbrtrd
    a1d
    ralrimiva
    @13
    @20
    vz
    c1
    crp
    @4
    c1
    wceq
    #
    @12
    @19
    vw
    chil
    @24
    @5
    @18
    @11
    @4
    c1
    @3
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    sylancr
    rgen2
    vx
    vy
    vz
    vw
    @0
    elcnfn
    mpbir2an
end
