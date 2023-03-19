include "cun.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "wrel.mm"
include "relfsupp.mm"
include "brrelex12.mm"
include "mpan.mm"
include "unexb.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wss.mm"
include "simpr.mm"
include "adantr.mm"
include "simprlr.mm"
include "suppun.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "wb.mm"
include "fununfun.mm"
include "simpld.mm"
include "simprll.mm"
include "adantl.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "uncom.mm"
include "oveq1i.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "simprd.mm"
include "jca.mm"
include "a1d.mm"
include "ex.mm"
include "fsuppimp.mm"
include "syl11.mm"
include "sylanbr.mm"
include "mpcom.mm"
include "com12.mm"
include "simpl.mm"
include "fsuppun.mm"
include "brrelexi.mm"
include "unexg.mm"
include "syl2an.mm"
include "brrelex2i.mm"
include "impbid.mm"

theorem fsuppunbi
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cZ: class Z
  assume fsuppunbi.u: |- ( ph -> Fun ( F u. G ) )


  assert |- ( ph -> ( ( F u. G ) finSupp Z <-> ( F finSupp Z /\ G finSupp Z ) ) )

  proof
    wph
    cF
    cG
    cun
    #
    cZ
    cfsupp
    wbr
    #
    cF
    cZ
    cfsupp
    wbr
    #
    cG
    cZ
    cfsupp
    wbr
    #
    wa
    #
    @1
    wph
    @4
    @0
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    wa
    #
    @1
    wph
    @4
    wi
    #
    cfsupp
    wrel
    @1
    @7
    relfsupp
    @0
    cZ
    cfsupp
    brrelex12
    mpan
    @5
    cF
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    wa
    #
    @6
    @1
    @8
    wi
    cF
    cG
    unexb
    @0
    wfun
    #
    @0
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    wa
    #
    @11
    @6
    wa
    #
    @8
    @1
    @15
    @16
    @8
    @15
    @16
    wa
    #
    @4
    wph
    @17
    @2
    @3
    @17
    @2
    cF
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    @17
    @14
    @18
    @13
    wss
    @19
    @15
    @14
    @16
    @12
    @14
    simpr
    adantr
    @17
    cF
    cG
    cvv
    cZ
    @15
    @9
    @10
    @6
    simprlr
    #
    suppun
    @13
    @18
    ssfi
    syl2anc
    @17
    cF
    wfun
    #
    @9
    @6
    @2
    @19
    wb
    @15
    @21
    @16
    @12
    @21
    @14
    @12
    @21
    cG
    wfun
    #
    cF
    cG
    fununfun
    #
    simpld
    adantr
    adantr
    @15
    @9
    @10
    @6
    simprll
    #
    @16
    @6
    @15
    @11
    @6
    simpr
    adantl
    #
    cF
    cvv
    cvv
    cZ
    funisfsupp
    syl3anc
    mpbird
    @17
    @3
    cG
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    @17
    cG
    cF
    cun
    #
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    @26
    @29
    wss
    @27
    @15
    @30
    @16
    @14
    @30
    @12
    @14
    @30
    @13
    @29
    cfn
    @0
    @28
    cZ
    csupp
    cF
    cG
    uncom
    oveq1i
    eleq1i
    biimpi
    adantl
    adantr
    @17
    cG
    cF
    cvv
    cZ
    @24
    suppun
    @29
    @26
    ssfi
    syl2anc
    @17
    @22
    @10
    @6
    @3
    @27
    wb
    @15
    @22
    @16
    @12
    @22
    @14
    @12
    @21
    @22
    @23
    simprd
    adantr
    adantr
    @20
    @25
    cG
    cvv
    cvv
    cZ
    funisfsupp
    syl3anc
    mpbird
    jca
    a1d
    ex
    @0
    cZ
    fsuppimp
    syl11
    sylanbr
    mpcom
    com12
    wph
    @4
    @1
    wph
    @4
    wa
    #
    @1
    @14
    @4
    @14
    wph
    @4
    cF
    cG
    cZ
    @2
    @3
    simpl
    @2
    @3
    simpr
    fsuppun
    adantl
    @31
    @12
    @5
    @6
    @1
    @14
    wb
    wph
    @12
    @4
    fsuppunbi.u
    adantr
    @4
    @5
    wph
    @2
    @9
    @10
    @5
    @3
    cF
    cZ
    cfsupp
    relfsupp
    brrelexi
    cG
    cZ
    cfsupp
    relfsupp
    brrelexi
    cF
    cG
    cvv
    cvv
    unexg
    syl2an
    adantl
    @4
    @6
    wph
    @2
    @6
    @3
    cF
    cZ
    cfsupp
    relfsupp
    brrelex2i
    adantr
    adantl
    @0
    cvv
    cvv
    cZ
    funisfsupp
    syl3anc
    mpbird
    ex
    impbid
end
