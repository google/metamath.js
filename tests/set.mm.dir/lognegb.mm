include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cneg.mm"
include "crp.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "cpi.mm"
include "wceq.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "logneg.mm"
include "fveq2d.mm"
include "cr.mm"
include "relogcl.mm"
include "pire.mm"
include "crim.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "negneg.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "syl5ib.mm"
include "cre.mm"
include "ce.mm"
include "c1.mm"
include "logcl.mm"
include "replimd.mm"
include "eflog.mm"
include "recld.mm"
include "recnd.mm"
include "ax-icn.mm"
include "imcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efadd.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "oveq2.mm"
include "efipi.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "syl5ibcom.mm"
include "rpefcld.mm"
include "rpcnd.mm"
include "neg1cn.mm"
include "mulcom.mm"
include "mulm1d.mm"
include "negeqd.mm"
include "negnegd.mm"
include "eqeltrd.mm"
include "negeq.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "impbid.mm"

theorem lognegb
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( -u A e. RR+ <-> ( Im ` ( log ` A ) ) = _pi ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cA
    cneg
    #
    crp
    wcel
    #
    cA
    clog
    cfv
    #
    cim
    cfv
    #
    cpi
    wceq
    #
    @4
    @3
    cneg
    #
    clog
    cfv
    #
    cim
    cfv
    #
    cpi
    wceq
    @2
    @7
    @4
    @10
    @3
    clog
    cfv
    #
    ci
    cpi
    cmul
    co
    #
    caddc
    co
    #
    cim
    cfv
    #
    cpi
    @4
    @9
    @13
    cim
    @3
    logneg
    fveq2d
    @4
    @11
    cr
    wcel
    cpi
    cr
    wcel
    @14
    cpi
    wceq
    @3
    relogcl
    pire
    @11
    cpi
    crim
    sylancl
    eqtrd
    @2
    @10
    @6
    cpi
    @2
    @9
    @5
    cim
    @2
    @8
    cA
    clog
    @0
    @8
    cA
    wceq
    @1
    cA
    negneg
    adantr
    fveq2d
    fveq2d
    eqeq1d
    syl5ib
    @2
    @7
    cA
    @5
    cre
    cfv
    #
    ce
    cfv
    #
    c1
    cneg
    #
    cmul
    co
    #
    wceq
    #
    @4
    @2
    cA
    @16
    ci
    @6
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    wceq
    @7
    @19
    @2
    @5
    ce
    cfv
    @15
    @20
    caddc
    co
    #
    ce
    cfv
    #
    cA
    @22
    @2
    @5
    @23
    ce
    @2
    @5
    cA
    logcl
    #
    replimd
    fveq2d
    cA
    eflog
    @2
    @15
    cc
    wcel
    @20
    cc
    wcel
    #
    @24
    @22
    wceq
    @2
    @15
    @2
    @5
    @25
    recld
    #
    recnd
    @2
    ci
    cc
    wcel
    @6
    cc
    wcel
    @26
    ax-icn
    @2
    @6
    @2
    @5
    @25
    imcld
    recnd
    ci
    @6
    mulcl
    sylancr
    @15
    @20
    efadd
    syl2anc
    3eqtr3d
    @7
    @22
    @18
    cA
    @7
    @21
    @17
    @16
    cmul
    @7
    @21
    @12
    ce
    cfv
    @17
    @7
    @20
    @12
    ce
    @6
    cpi
    ci
    cmul
    oveq2
    fveq2d
    efipi
    syl6eq
    oveq2d
    eqeq2d
    syl5ibcom
    @2
    @4
    @19
    @18
    cneg
    #
    crp
    wcel
    @2
    @28
    @16
    crp
    @2
    @28
    @16
    cneg
    #
    cneg
    @16
    @2
    @18
    @29
    @2
    @18
    @17
    @16
    cmul
    co
    #
    @29
    @2
    @16
    cc
    wcel
    @17
    cc
    wcel
    @18
    @30
    wceq
    @2
    @16
    @2
    @15
    @27
    rpefcld
    #
    rpcnd
    #
    neg1cn
    @16
    @17
    mulcom
    sylancl
    @2
    @16
    @32
    mulm1d
    eqtrd
    negeqd
    @2
    @16
    @32
    negnegd
    eqtrd
    @31
    eqeltrd
    @19
    @3
    @28
    crp
    cA
    @18
    negeq
    eleq1d
    syl5ibrcom
    syld
    impbid
end
