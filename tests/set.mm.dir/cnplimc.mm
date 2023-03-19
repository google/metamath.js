include "cc.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wf.mm"
include "climc.mm"
include "ctopon.mm"
include "wi.mm"
include "crest.mm"
include "cnfldtopon.mm"
include "simpl.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "cnpf2.mm"
include "3expia.mm"
include "sylancl.mm"
include "pm4.71rd.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "cmpt.mm"
include "simpr.mm"
include "wceq.mm"
include "simplr.mm"
include "snssd.mm"
include "ssequn2.mm"
include "sylib.mm"
include "feq2d.mm"
include "mpbird.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "syl6reqr.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "eleq12d.mm"
include "eqid.mm"
include "cif.mm"
include "ifid.mm"
include "fveq2.mm"
include "adantl.mm"
include "ifeq1da.mm"
include "syl5eqr.mm"
include "mpteq2ia.mm"
include "simpll.mm"
include "sseldd.mm"
include "ellimc.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem cnplimc
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let vx: setvar x
  assume cnplimc.k: |- K = ( TopOpen ` CCfld )
  assume cnplimc.j: |- J = ( K |`t A )


  assert |- ( ( A C_ CC /\ B e. A ) -> ( F e. ( ( J CnP K ) ` B ) <-> ( F : A --> CC /\ ( F ` B ) e. ( F limCC B ) ) ) )

  proof
    cA
    cc
    wss
    #
    cB
    cA
    wcel
    #
    wa
    #
    cF
    cB
    cJ
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    cA
    cc
    cF
    wf
    #
    @5
    wa
    @6
    cB
    cF
    cfv
    #
    cF
    cB
    climc
    co
    wcel
    #
    wa
    @2
    @5
    @6
    @2
    cJ
    cA
    ctopon
    cfv
    #
    wcel
    #
    cK
    cc
    ctopon
    cfv
    wcel
    #
    @5
    @6
    wi
    @2
    cJ
    cK
    cA
    crest
    co
    #
    @9
    cnplimc.j
    @2
    @11
    @0
    @12
    @9
    wcel
    cK
    cnplimc.k
    cnfldtopon
    #
    @0
    @1
    simpl
    cA
    cK
    cc
    resttopon
    sylancr
    syl5eqel
    @13
    @10
    @11
    @5
    @6
    cB
    cF
    cJ
    cK
    cA
    cc
    cnpf2
    3expia
    sylancl
    pm4.71rd
    @2
    @6
    @5
    @8
    @2
    @6
    wa
    #
    @5
    vx
    cA
    cB
    csn
    #
    cun
    #
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cB
    cK
    @16
    crest
    co
    #
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    @8
    @14
    cF
    @19
    @4
    @22
    @14
    vx
    @16
    cc
    cF
    @14
    @16
    cc
    cF
    wf
    @6
    @2
    @6
    simpr
    #
    @14
    @16
    cA
    cc
    cF
    @14
    @15
    cA
    wss
    @16
    cA
    wceq
    @14
    cB
    cA
    @0
    @1
    @6
    simplr
    #
    snssd
    @15
    cA
    ssequn2
    sylib
    #
    feq2d
    mpbird
    feqmptd
    @14
    cB
    @3
    @21
    @14
    cJ
    @20
    cK
    ccnp
    @14
    @20
    @12
    cJ
    @14
    @16
    cA
    cK
    crest
    @25
    oveq2d
    cnplimc.j
    syl6reqr
    oveq1d
    fveq1d
    eleq12d
    @14
    vx
    cA
    cB
    @7
    cF
    @19
    @20
    cK
    @20
    eqid
    cnplimc.k
    vx
    @16
    @18
    @17
    cB
    wceq
    #
    @7
    @18
    cif
    #
    @17
    @16
    wcel
    #
    @18
    @26
    @18
    @18
    cif
    @27
    @26
    @18
    ifid
    @28
    @26
    @18
    @7
    @18
    @26
    @18
    @7
    wceq
    @28
    @17
    cB
    cF
    fveq2
    adantl
    ifeq1da
    syl5eqr
    mpteq2ia
    @23
    @0
    @1
    @6
    simpll
    #
    @14
    cA
    cc
    cB
    @29
    @24
    sseldd
    ellimc
    bitr4d
    pm5.32da
    bitrd
end
