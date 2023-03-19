include "cmgm.mm"
include "wcel.mm"
include "csubmgm.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "eqid.mm"
include "issubmgm.mm"
include "cvv.mm"
include "cbs.mm"
include "wceq.mm"
include "ressbas2.mm"
include "ad2antlr.mm"
include "cress.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fvex.mm"
include "ssex.mm"
include "ressplusg.mm"
include "syl.mm"
include "wi.mm"
include "weq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "com12.mm"
include "adantl.mm"
include "3impib.mm"
include "ismgmd.mm"
include "simplr.mm"
include "simprl.mm"
include "ad3antlr.mm"
include "eleqtrd.mm"
include "simpr.mm"
include "mgmcl.mm"
include "syl3anc.mm"
include "oveqdr.mm"
include "3eltr4d.mm"
include "ralrimivva.mm"
include "impbida.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem issubmgm2
  let cB: class B
  let cS: class S
  let cH: class H
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume issubmgm2.b: |- B = ( Base ` M )
  assume issubmgm2.h: |- H = ( M |`s S )


  assert |- ( M e. Mgm -> ( S e. ( SubMgm ` M ) <-> ( S C_ B /\ H e. Mgm ) ) )

  proof
    cM
    cmgm
    wcel
    #
    cS
    cM
    csubmgm
    cfv
    wcel
    cS
    cB
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    cS
    wcel
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    wa
    @1
    cH
    cmgm
    wcel
    #
    wa
    vx
    vy
    cB
    @4
    cS
    cM
    issubmgm2.b
    @4
    eqid
    #
    issubmgm
    @0
    @1
    @7
    @8
    @0
    @1
    wa
    #
    @7
    @8
    @10
    @7
    wa
    #
    va
    vb
    cS
    @4
    cH
    cvv
    @1
    cS
    cH
    cbs
    cfv
    #
    wceq
    #
    @0
    @7
    cS
    cB
    cH
    cM
    issubmgm2.h
    issubmgm2.b
    ressbas2
    #
    ad2antlr
    cH
    cvv
    wcel
    @11
    cH
    cM
    cS
    cress
    co
    cvv
    issubmgm2.h
    cM
    cS
    cress
    ovex
    eqeltri
    a1i
    @11
    cS
    cvv
    wcel
    #
    @4
    cH
    cplusg
    cfv
    #
    wceq
    #
    @1
    @15
    @0
    @7
    cS
    cB
    cB
    cM
    cbs
    cfv
    cvv
    issubmgm2.b
    cM
    cbs
    fvex
    eqeltri
    ssex
    #
    ad2antlr
    cS
    @4
    cM
    cH
    cvv
    issubmgm2.h
    @9
    ressplusg
    #
    syl
    @11
    va
    cv
    #
    cS
    wcel
    #
    vb
    cv
    #
    cS
    wcel
    #
    @20
    @22
    @4
    co
    #
    cS
    wcel
    #
    @7
    @21
    @23
    wa
    #
    @25
    wi
    @10
    @26
    @7
    @25
    @6
    @25
    @20
    @3
    @4
    co
    #
    cS
    wcel
    vx
    vy
    @20
    @22
    cS
    cS
    vx
    va
    weq
    @5
    @27
    cS
    @2
    @20
    @3
    @4
    oveq1
    eleq1d
    vy
    vb
    weq
    @27
    @24
    cS
    @3
    @22
    @20
    @4
    oveq2
    eleq1d
    rspc2v
    com12
    adantl
    3impib
    ismgmd
    @10
    @8
    wa
    #
    @6
    vx
    vy
    cS
    cS
    @28
    @2
    cS
    wcel
    #
    @3
    cS
    wcel
    #
    wa
    #
    wa
    #
    @2
    @3
    @16
    co
    #
    @12
    @5
    cS
    @32
    @8
    @2
    @12
    wcel
    @3
    @12
    wcel
    @33
    @12
    wcel
    @10
    @8
    @31
    simplr
    @32
    @2
    cS
    @12
    @28
    @29
    @30
    simprl
    @1
    @13
    @0
    @8
    @31
    @14
    ad3antlr
    #
    eleqtrd
    @32
    @3
    cS
    @12
    @31
    @30
    @28
    @29
    @30
    simpr
    adantl
    @34
    eleqtrd
    @12
    cH
    @2
    @3
    @16
    @12
    eqid
    @16
    eqid
    mgmcl
    syl3anc
    @28
    @31
    vx
    vy
    @4
    @16
    @28
    @15
    @17
    @1
    @15
    @0
    @8
    @18
    ad2antlr
    @19
    syl
    oveqdr
    @34
    3eltr4d
    ralrimivva
    impbida
    pm5.32da
    bitrd
end
