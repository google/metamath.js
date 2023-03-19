include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "c1.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "crn.mm"
include "cc0.mm"
include "cre.mm"
include "0red.mm"
include "cc.mm"
include "wne.mm"
include "atandm2.mm"
include "simp1bi.mm"
include "recld.mm"
include "atanlogaddlem.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcl.mm"
include "simp3bi.mm"
include "logcld.mm"
include "subcl.mm"
include "simp2bi.mm"
include "addcomd.mm"
include "mulneg2.mm"
include "oveq2d.mm"
include "negsub.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "subneg.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "atandmneg.mm"
include "le0neg1d.mm"
include "biimpa.mm"
include "renegd.mm"
include "breqtrrd.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "lecasei.mm"

theorem atanlogadd
  let cA: class A


  assert |- ( A e. dom arctan -> ( ( log ` ( 1 + ( _i x. A ) ) ) + ( log ` ( 1 - ( _i x. A ) ) ) ) e. ran log )

  proof
    cA
    catan
    cdm
    #
    wcel
    #
    c1
    ci
    cA
    cmul
    co
    #
    caddc
    co
    #
    clog
    cfv
    #
    c1
    @2
    cmin
    co
    #
    clog
    cfv
    #
    caddc
    co
    #
    clog
    crn
    #
    wcel
    cc0
    cA
    cre
    cfv
    #
    @1
    0red
    @1
    cA
    @1
    cA
    cc
    wcel
    #
    @5
    cc0
    wne
    #
    @3
    cc0
    wne
    #
    cA
    atandm2
    #
    simp1bi
    #
    recld
    #
    cA
    atanlogaddlem
    @1
    @9
    cc0
    cle
    wbr
    #
    wa
    #
    @7
    c1
    ci
    cA
    cneg
    #
    cmul
    co
    #
    caddc
    co
    #
    clog
    cfv
    #
    c1
    @19
    cmin
    co
    #
    clog
    cfv
    #
    caddc
    co
    #
    @8
    @1
    @7
    @24
    wceq
    @16
    @1
    @7
    @6
    @4
    caddc
    co
    @24
    @1
    @4
    @6
    @1
    @3
    @1
    c1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @3
    cc
    wcel
    ax-1cn
    @1
    ci
    cc
    wcel
    #
    @10
    @26
    ax-icn
    @14
    ci
    cA
    mulcl
    sylancr
    #
    c1
    @2
    addcl
    sylancr
    @1
    @10
    @11
    @12
    @13
    simp3bi
    logcld
    @1
    @5
    @1
    @25
    @26
    @5
    cc
    wcel
    ax-1cn
    @28
    c1
    @2
    subcl
    sylancr
    @1
    @10
    @11
    @12
    @13
    simp2bi
    logcld
    addcomd
    @1
    @21
    @6
    @23
    @4
    caddc
    @1
    @20
    @5
    clog
    @1
    @20
    c1
    @2
    cneg
    #
    caddc
    co
    #
    @5
    @1
    @19
    @29
    c1
    caddc
    @1
    @27
    @10
    @19
    @29
    wceq
    ax-icn
    @14
    ci
    cA
    mulneg2
    sylancr
    #
    oveq2d
    @1
    @25
    @26
    @30
    @5
    wceq
    ax-1cn
    @28
    c1
    @2
    negsub
    sylancr
    eqtrd
    fveq2d
    @1
    @22
    @3
    clog
    @1
    @22
    c1
    @29
    cmin
    co
    #
    @3
    @1
    @19
    @29
    c1
    cmin
    @31
    oveq2d
    @1
    @25
    @26
    @32
    @3
    wceq
    ax-1cn
    @28
    c1
    @2
    subneg
    sylancr
    eqtrd
    fveq2d
    oveq12d
    eqtr4d
    adantr
    @17
    @18
    @0
    wcel
    #
    cc0
    @18
    cre
    cfv
    #
    cle
    wbr
    @24
    @8
    wcel
    @1
    @33
    @16
    cA
    atandmneg
    adantr
    @17
    cc0
    @9
    cneg
    #
    @34
    cle
    @1
    @16
    cc0
    @35
    cle
    wbr
    @1
    @9
    @15
    le0neg1d
    biimpa
    @1
    @34
    @35
    wceq
    @16
    @1
    cA
    @14
    renegd
    adantr
    breqtrrd
    @18
    atanlogaddlem
    syl2anc
    eqeltrd
    lecasei
end
