include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "crg.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "wss.mm"
include "cur.mm"
include "simpl.mm"
include "subrgrcl.mm"
include "adantl.mm"
include "psrring.mm"
include "subrgring.mm"
include "wceq.mm"
include "a1i.mm"
include "eqid.mm"
include "simpr.mm"
include "resspsrbas.mm"
include "cv.mm"
include "resspsradd.mm"
include "resspsrmul.mm"
include "ringpropd.mm"
include "mpbid.mm"
include "jca.mm"
include "ressbasss.mm"
include "syl6eqss.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "wf.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt.mm"
include "subrg1cl.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "subg0cl.mm"
include "syl.mm"
include "ifcld.mm"
include "subrgbas.mm"
include "eleqtrd.mm"
include "adantr.mm"
include "fmptd.mm"
include "psr1.mm"
include "feq1d.mm"
include "mpbird.mm"
include "fvex.mm"
include "ovex.mm"
include "rabex.mm"
include "elmap.mm"
include "sylibr.mm"
include "psrbas.mm"
include "eleqtrrd.mm"
include "issubrg.mm"
include "sylanbrc.mm"

theorem subrgpsr
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assume subrgpsr.s: |- S = ( I mPwSer R )
  assume subrgpsr.h: |- H = ( R |`s T )
  assume subrgpsr.u: |- U = ( I mPwSer H )
  assume subrgpsr.b: |- B = ( Base ` U )


  assert |- ( ( I e. V /\ T e. ( SubRing ` R ) ) -> B e. ( SubRing ` S ) )

  proof
    cI
    cV
    wcel
    #
    cT
    cR
    csubrg
    cfv
    wcel
    #
    wa
    #
    cS
    crg
    wcel
    #
    cS
    cB
    cress
    co
    #
    crg
    wcel
    #
    wa
    cB
    cS
    cbs
    cfv
    #
    wss
    #
    cS
    cur
    cfv
    #
    cB
    wcel
    #
    wa
    cB
    cS
    csubrg
    cfv
    wcel
    @2
    @3
    @5
    @2
    cR
    cS
    cI
    cV
    subrgpsr.s
    @0
    @1
    simpl
    #
    @1
    cR
    crg
    wcel
    @0
    cT
    cR
    subrgrcl
    adantl
    #
    psrring
    @2
    cU
    crg
    wcel
    @5
    @2
    cH
    cU
    cI
    cV
    subrgpsr.u
    @10
    @1
    cH
    crg
    wcel
    @0
    cT
    cR
    cH
    subrgpsr.h
    subrgring
    adantl
    psrring
    @2
    vx
    vy
    cB
    cU
    @4
    cB
    cU
    cbs
    cfv
    wceq
    @2
    subrgpsr.b
    a1i
    @2
    cB
    @4
    cR
    cS
    cT
    cU
    cH
    cI
    subrgpsr.s
    subrgpsr.h
    subrgpsr.u
    subrgpsr.b
    @4
    eqid
    #
    @0
    @1
    simpr
    #
    resspsrbas
    #
    @2
    cB
    @4
    cR
    cS
    cT
    cU
    cH
    cI
    vx
    cv
    #
    vy
    cv
    #
    subrgpsr.s
    subrgpsr.h
    subrgpsr.u
    subrgpsr.b
    @12
    @13
    resspsradd
    @2
    cB
    @4
    cR
    cS
    cT
    cU
    cH
    cI
    @15
    @16
    subrgpsr.s
    subrgpsr.h
    subrgpsr.u
    subrgpsr.b
    @12
    @13
    resspsrmul
    ringpropd
    mpbid
    jca
    @2
    @7
    @9
    @2
    cB
    @4
    cbs
    cfv
    @6
    @14
    cB
    @6
    @4
    cS
    @12
    @6
    eqid
    #
    ressbasss
    syl6eqss
    @2
    @8
    cH
    cbs
    cfv
    #
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vf
    cn0
    cI
    cmap
    co
    #
    crab
    #
    cmap
    co
    #
    cB
    @2
    @21
    @18
    @8
    wf
    #
    @8
    @22
    wcel
    @2
    @23
    @21
    @18
    vx
    @21
    @15
    cI
    cc0
    csn
    cxp
    wceq
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    wf
    @2
    vx
    @21
    @27
    @18
    @28
    @2
    @27
    @18
    wcel
    @15
    @21
    wcel
    @2
    @27
    cT
    @18
    @1
    @27
    cT
    wcel
    @0
    @1
    @24
    @25
    @26
    cT
    cT
    cR
    @25
    @25
    eqid
    #
    subrg1cl
    @1
    cT
    cR
    csubg
    cfv
    wcel
    @26
    cT
    wcel
    cT
    cR
    subrgsubg
    cT
    cR
    @26
    @26
    eqid
    #
    subg0cl
    syl
    ifcld
    adantl
    @1
    cT
    @18
    wceq
    @0
    cT
    cR
    cH
    subrgpsr.h
    subrgbas
    adantl
    eleqtrd
    adantr
    @28
    eqid
    fmptd
    @2
    @21
    @18
    @8
    @28
    @2
    vx
    @21
    cR
    cS
    @8
    @25
    vf
    cI
    cV
    @26
    subrgpsr.s
    @10
    @11
    @21
    eqid
    #
    @30
    @29
    @8
    eqid
    #
    psr1
    feq1d
    mpbird
    @18
    @21
    @8
    cH
    cbs
    fvex
    @19
    vf
    @20
    cn0
    cI
    cmap
    ovex
    rabex
    elmap
    sylibr
    @2
    cB
    @21
    cH
    cU
    vf
    cI
    @18
    cV
    subrgpsr.u
    @18
    eqid
    @31
    subrgpsr.b
    @10
    psrbas
    eleqtrrd
    jca
    cB
    @6
    cS
    @8
    @17
    @32
    issubrg
    sylanbrc
end
