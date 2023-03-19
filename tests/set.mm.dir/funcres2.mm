include "csubc.mm"
include "cfv.mm"
include "wcel.mm"
include "cresc.mm"
include "co.mm"
include "cfunc.mm"
include "wrel.mm"
include "relfunc.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wa.mm"
include "simpr.mm"
include "cbs.mm"
include "cdm.mm"
include "chom.mm"
include "eqid.mm"
include "simpl.mm"
include "eqidd.mm"
include "subcfn.mm"
include "wf.mm"
include "funcf1.mm"
include "ccat.mm"
include "subcrcl.mm"
include "adantr.mm"
include "subcss1.mm"
include "rescbas.mm"
include "feq3d.mm"
include "mpbird.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "funcf2.mm"
include "wceq.mm"
include "reschom.mm"
include "oveqd.mm"
include "funcres2b.mm"
include "ex.mm"
include "df-br.mm"
include "3imtr3g.mm"
include "relssdv.mm"

theorem funcres2
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. ( Subcat ` D ) -> ( C Func ( D |`cat R ) ) C_ ( C Func D ) )

  proof
    cR
    cD
    csubc
    cfv
    wcel
    #
    vf
    vg
    cC
    cD
    cR
    cresc
    co
    #
    cfunc
    co
    #
    cC
    cD
    cfunc
    co
    #
    @2
    wrel
    @0
    cC
    @1
    relfunc
    a1i
    @0
    vf
    cv
    #
    vg
    cv
    #
    @2
    wbr
    #
    @4
    @5
    @3
    wbr
    #
    @4
    @5
    cop
    #
    @2
    wcel
    @8
    @3
    wcel
    @0
    @6
    @7
    @0
    @6
    wa
    #
    @7
    @6
    @0
    @6
    simpr
    #
    @9
    vx
    vy
    cC
    cbs
    cfv
    #
    cC
    cD
    cR
    cR
    cdm
    cdm
    #
    @4
    @5
    cC
    chom
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    @13
    co
    #
    @11
    eqid
    #
    @13
    eqid
    #
    @0
    @6
    simpl
    #
    @9
    cD
    @12
    cR
    @19
    @9
    @12
    eqidd
    subcfn
    #
    @9
    @11
    @12
    @4
    wf
    @11
    @1
    cbs
    cfv
    #
    @4
    wf
    @9
    @11
    @21
    cC
    @1
    @4
    @5
    @17
    @21
    eqid
    @10
    funcf1
    @9
    @12
    @21
    @4
    @11
    @9
    cD
    cbs
    cfv
    #
    cD
    @1
    @12
    cR
    ccat
    @1
    eqid
    #
    @22
    eqid
    #
    @0
    cD
    ccat
    wcel
    @6
    cD
    cR
    subcrcl
    adantr
    #
    @20
    @9
    @22
    cD
    @12
    cR
    @19
    @20
    @24
    subcss1
    #
    rescbas
    feq3d
    mpbird
    @9
    @14
    @11
    wcel
    #
    @15
    @11
    wcel
    #
    wa
    #
    wa
    #
    @16
    @14
    @4
    cfv
    #
    @15
    @4
    cfv
    #
    cR
    co
    #
    @14
    @15
    @5
    co
    #
    wf
    @16
    @31
    @32
    @1
    chom
    cfv
    #
    co
    #
    @34
    wf
    @30
    @11
    cC
    @1
    @4
    @5
    @13
    @35
    @14
    @15
    @17
    @18
    @35
    eqid
    @0
    @6
    @29
    simplr
    @9
    @27
    @28
    simprl
    @9
    @27
    @28
    simprr
    funcf2
    @30
    @33
    @36
    @34
    @16
    @30
    cR
    @35
    @31
    @32
    @9
    cR
    @35
    wceq
    @29
    @9
    @22
    cD
    @1
    @12
    cR
    ccat
    @23
    @24
    @25
    @20
    @26
    reschom
    adantr
    oveqd
    feq3d
    mpbird
    funcres2b
    mpbird
    ex
    @4
    @5
    @2
    df-br
    @4
    @5
    @3
    df-br
    3imtr3g
    relssdv
end
