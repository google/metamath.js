include "crp.mm"
include "wcel.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "csu.mm"
include "ccht.mm"
include "cppi.mm"
include "cmul.mm"
include "cle.mm"
include "cr.mm"
include "cfn.mm"
include "rpre.mm"
include "ppifi.mm"
include "syl.mm"
include "wa.mm"
include "cn.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "relogcl.mm"
include "adantr.mm"
include "wbr.mm"
include "ce.mm"
include "w3a.mm"
include "inss1.mm"
include "wb.mm"
include "0re.mm"
include "elicc2.mm"
include "sylancr.mm"
include "biimpa.mm"
include "syldan.mm"
include "simp3d.mm"
include "reeflogd.mm"
include "wceq.mm"
include "reeflog.mm"
include "3brtr4d.mm"
include "efle.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "fsumle.mm"
include "chtval.mm"
include "chash.mm"
include "ppival.mm"
include "oveq1d.mm"
include "cc.mm"
include "recnd.mm"
include "fsumconst.mm"
include "eqtr4d.mm"

theorem chtleppi
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  let cN: class N


  assert |- ( A e. RR+ -> ( theta ` A ) <_ ( ( ppi ` A ) x. ( log ` A ) ) )

  proof
    cA
    crp
    wcel
    #
    cc0
    cA
    cicc
    co
    #
    cprime
    cin
    #
    vp
    cv
    #
    clog
    cfv
    #
    vp
    csu
    #
    @2
    cA
    clog
    cfv
    #
    vp
    csu
    #
    cA
    ccht
    cfv
    #
    cA
    cppi
    cfv
    #
    @6
    cmul
    co
    #
    cle
    @0
    @2
    @4
    @6
    vp
    @0
    cA
    cr
    wcel
    #
    @2
    cfn
    wcel
    #
    cA
    rpre
    #
    cA
    ppifi
    syl
    #
    @0
    @3
    @2
    wcel
    #
    wa
    #
    @3
    @16
    @3
    @16
    @3
    cprime
    wcel
    @3
    cn
    wcel
    @16
    @2
    cprime
    @3
    @1
    cprime
    inss2
    @0
    @15
    simpr
    #
    sseldi
    @3
    prmnn
    syl
    nnrpd
    #
    relogcld
    #
    @0
    @6
    cr
    wcel
    #
    @15
    cA
    relogcl
    #
    adantr
    #
    @16
    @4
    @6
    cle
    wbr
    #
    @4
    ce
    cfv
    #
    @6
    ce
    cfv
    #
    cle
    wbr
    #
    @16
    @3
    cA
    @24
    @25
    cle
    @16
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @3
    cA
    cle
    wbr
    #
    @0
    @15
    @3
    @1
    wcel
    #
    @27
    @28
    @29
    w3a
    #
    @16
    @2
    @1
    @3
    @1
    cprime
    inss1
    @17
    sseldi
    @0
    @30
    @31
    @0
    cc0
    cr
    wcel
    @11
    @30
    @31
    wb
    0re
    @13
    cc0
    cA
    @3
    elicc2
    sylancr
    biimpa
    syldan
    simp3d
    @16
    @3
    @18
    reeflogd
    @0
    @25
    cA
    wceq
    @15
    cA
    reeflog
    adantr
    3brtr4d
    @16
    @4
    cr
    wcel
    @20
    @23
    @26
    wb
    @19
    @22
    @4
    @6
    efle
    syl2anc
    mpbird
    fsumle
    @0
    @11
    @8
    @5
    wceq
    @13
    cA
    vp
    chtval
    syl
    @0
    @10
    @2
    chash
    cfv
    #
    @6
    cmul
    co
    #
    @7
    @0
    @9
    @32
    @6
    cmul
    @0
    @11
    @9
    @32
    wceq
    @13
    cA
    ppival
    syl
    oveq1d
    @0
    @12
    @6
    cc
    wcel
    @7
    @33
    wceq
    @14
    @0
    @6
    @21
    recnd
    @2
    @6
    vp
    fsumconst
    syl2anc
    eqtr4d
    3brtr4d
end
