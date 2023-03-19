include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wa.mm"
include "cn0.mm"
include "c1st.mm"
include "chash.mm"
include "wceq.mm"
include "c2nd.mm"
include "cwwlksn.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cvtx.mm"
include "cword.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "cc0.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wbr.mm"
include "wlkcpr.mm"
include "wlkn0.mm"
include "sylbi.mm"
include "adantl.mm"
include "ciedg.mm"
include "cdm.mm"
include "cfz.mm"
include "wf.mm"
include "eqid.mm"
include "wlkelwrd.mm"
include "ffz0iswrd.mm"
include "syl.mm"
include "upgrwlkvtxedg.mm"
include "wlklenvm1.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "mpbid.mm"
include "sylan2b.mm"
include "3jca.mm"
include "adantr.mm"
include "wi.mm"
include "simpl.mm"
include "oveq2.mm"
include "feq2d.mm"
include "biimpd.mm"
include "impancom.mm"
include "adantld.mm"
include "imp.mm"
include "ffz0hash.mm"
include "syl2an2.mm"
include "ex.mm"
include "wb.mm"
include "cwwlks.mm"
include "iswwlksn.mm"
include "iswwlks.mm"
include "a1i.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "mpbir2and.mm"

theorem wlknewwlksn
  let cG: class G
  let cN: class N
  let cW: class W
  let vi: setvar i


  assert |- ( ( ( G e. UPGraph /\ W e. ( Walks ` G ) ) /\ ( N e. NN0 /\ ( # ` ( 1st ` W ) ) = N ) ) -> ( 2nd ` W ) e. ( N WWalksN G ) )

  proof
    cG
    cupgr
    wcel
    #
    cW
    cG
    cwlks
    cfv
    #
    wcel
    #
    wa
    #
    cN
    cn0
    wcel
    #
    cW
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    wa
    #
    cW
    c2nd
    cfv
    #
    cN
    cG
    cwwlksn
    co
    wcel
    #
    @10
    c0
    wne
    #
    @10
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    vi
    cv
    #
    @10
    cfv
    @15
    c1
    caddc
    co
    @10
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    #
    vi
    cc0
    @10
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @18
    cN
    c1
    caddc
    co
    wceq
    #
    @3
    @22
    @8
    @3
    @12
    @14
    @21
    @2
    @12
    @0
    @2
    @5
    @10
    @1
    wbr
    #
    @12
    cG
    cW
    wlkcpr
    #
    @10
    @5
    cG
    wlkn0
    sylbi
    adantl
    @2
    @14
    @0
    @2
    @5
    cG
    ciedg
    cfv
    #
    cdm
    cword
    wcel
    #
    cc0
    @6
    cfz
    co
    #
    @13
    @10
    wf
    #
    wa
    #
    @14
    @10
    @5
    cG
    @26
    @13
    cW
    @13
    eqid
    #
    @26
    eqid
    @5
    eqid
    @10
    eqid
    wlkelwrd
    #
    @29
    @14
    @27
    @13
    @6
    @10
    ffz0iswrd
    adantl
    syl
    adantl
    @2
    @0
    @24
    @21
    @25
    @0
    @24
    wa
    #
    @17
    vi
    cc0
    @6
    cfzo
    co
    #
    wral
    @21
    @10
    vi
    @16
    @5
    cG
    @16
    eqid
    #
    upgrwlkvtxedg
    @33
    @17
    vi
    @34
    @20
    @33
    @6
    @19
    cc0
    cfzo
    @24
    @6
    @19
    wceq
    @0
    @10
    @5
    cG
    wlklenvm1
    adantl
    oveq2d
    raleqdv
    mpbid
    sylan2b
    3jca
    adantr
    @3
    @8
    @23
    @2
    @8
    @23
    wi
    #
    @0
    @2
    @30
    @36
    @32
    @30
    @8
    @23
    @8
    @4
    @30
    cc0
    cN
    cfz
    co
    #
    @13
    @10
    wf
    #
    @23
    @4
    @7
    simpl
    #
    @30
    @8
    @38
    @30
    @7
    @38
    @4
    @27
    @7
    @29
    @38
    @27
    @7
    wa
    #
    @29
    @38
    @40
    @28
    @37
    @13
    @10
    @7
    @28
    @37
    wceq
    @27
    @6
    cN
    cc0
    cfz
    oveq2
    adantl
    feq2d
    biimpd
    impancom
    adantld
    imp
    @13
    @10
    cN
    ffz0hash
    syl2an2
    ex
    syl
    adantl
    imp
    @9
    @4
    @11
    @22
    @23
    wa
    #
    wb
    @8
    @4
    @3
    @39
    adantl
    @4
    @11
    @10
    cG
    cwwlks
    cfv
    wcel
    #
    @23
    wa
    @41
    cG
    cN
    @10
    iswwlksn
    @4
    @42
    @22
    @23
    @42
    @22
    wb
    @4
    vi
    @16
    cG
    @13
    @10
    @31
    @35
    iswwlks
    a1i
    anbi1d
    bitrd
    syl
    mpbir2and
end
