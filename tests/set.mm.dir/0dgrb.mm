include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cdgr.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "csn.mm"
include "cxp.mm"
include "wa.mm"
include "ccoe.mm"
include "cmpt.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "eqid.mm"
include "coeid.mm"
include "adantr.mm"
include "simplr.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "cz.mm"
include "0z.mm"
include "c1.mm"
include "exp0.mm"
include "adantl.mm"
include "cn0.mm"
include "wf.mm"
include "coef3.mm"
include "0nn0.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "ad2antrr.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fsum1.mm"
include "sylancr.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "0cn.mm"
include "fvex.mm"
include "fvconst2.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "eqtr4d.mm"
include "ex.mm"
include "plyf.mm"
include "0dgr.mm"
include "syl.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem 0dgrb
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vz: setvar z
  let cA: class A


  assert |- ( F e. ( Poly ` S ) -> ( ( deg ` F ) = 0 <-> F = ( CC X. { ( F ` 0 ) } ) ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cF
    cdgr
    cfv
    #
    cc0
    wceq
    #
    cF
    cc
    cc0
    cF
    cfv
    #
    csn
    #
    cxp
    #
    wceq
    #
    @0
    @2
    @6
    @0
    @2
    wa
    #
    cF
    cc
    cc0
    cF
    ccoe
    cfv
    #
    cfv
    #
    csn
    #
    cxp
    #
    @5
    @7
    cF
    vz
    cc
    @9
    cmpt
    #
    @11
    @7
    cF
    vz
    cc
    cc0
    @1
    cfz
    co
    #
    vk
    cv
    #
    @8
    cfv
    #
    vz
    cv
    #
    @14
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    @12
    @0
    cF
    @20
    wceq
    @2
    vz
    @8
    cS
    vk
    cF
    @1
    @8
    eqid
    #
    @1
    eqid
    coeid
    adantr
    @7
    vz
    cc
    @19
    @9
    @7
    @16
    cc
    wcel
    #
    wa
    #
    @19
    cc0
    cc0
    cfz
    co
    #
    @18
    vk
    csu
    #
    @9
    @23
    @13
    @24
    @18
    vk
    @23
    @1
    cc0
    cc0
    cfz
    @0
    @2
    @22
    simplr
    oveq2d
    sumeq1d
    @23
    @25
    @9
    @16
    cc0
    cexp
    co
    #
    cmul
    co
    #
    @9
    @23
    cc0
    cz
    wcel
    @27
    cc
    wcel
    @25
    @27
    wceq
    0z
    @23
    @27
    @9
    cc
    @23
    @27
    @9
    c1
    cmul
    co
    @9
    @23
    @26
    c1
    @9
    cmul
    @22
    @26
    c1
    wceq
    @7
    @16
    exp0
    adantl
    oveq2d
    @23
    @9
    @0
    @9
    cc
    wcel
    #
    @2
    @22
    @0
    cn0
    cc
    @8
    wf
    cc0
    cn0
    wcel
    @28
    @8
    cS
    cF
    @21
    coef3
    0nn0
    cn0
    cc
    cc0
    @8
    ffvelrn
    sylancl
    ad2antrr
    #
    mulid1d
    eqtrd
    #
    @29
    eqeltrd
    @18
    @27
    vk
    cc0
    @14
    cc0
    wceq
    @15
    @9
    @17
    @26
    cmul
    @14
    cc0
    @8
    fveq2
    @14
    cc0
    @16
    cexp
    oveq2
    oveq12d
    fsum1
    sylancr
    @30
    eqtrd
    eqtrd
    mpteq2dva
    eqtrd
    vz
    cc
    @9
    fconstmpt
    syl6eqr
    #
    @7
    @4
    @10
    cc
    @7
    @3
    @9
    @7
    @3
    cc0
    @11
    cfv
    #
    @9
    @7
    cc0
    cF
    @11
    @31
    fveq1d
    cc0
    cc
    wcel
    #
    @32
    @9
    wceq
    0cn
    cc
    @9
    cc0
    cc0
    @8
    fvex
    fvconst2
    ax-mp
    syl6eq
    sneqd
    xpeq2d
    eqtr4d
    ex
    @0
    @2
    @6
    @5
    cdgr
    cfv
    #
    cc0
    wceq
    #
    @0
    @3
    cc
    wcel
    #
    @35
    @0
    cc
    cc
    cF
    wf
    @33
    @36
    cS
    cF
    plyf
    0cn
    cc
    cc
    cc0
    cF
    ffvelrn
    sylancl
    @3
    0dgr
    syl
    @6
    @1
    @34
    cc0
    cF
    @5
    cdgr
    fveq2
    eqeq1d
    syl5ibrcom
    impbid
end
