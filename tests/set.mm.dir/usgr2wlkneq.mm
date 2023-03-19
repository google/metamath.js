include "cusgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "w3a.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "caddc.mm"
include "cpr.mm"
include "cfzo.mm"
include "wral.mm"
include "wi.mm"
include "cupgr.mm"
include "wb.mm"
include "usgrupgr.mm"
include "eqid.mm"
include "upgriswlk.mm"
include "syl.mm"
include "2wlklem.mm"
include "cvv.mm"
include "simplll.mm"
include "fvex.mm"
include "usgrnloopv.mm"
include "sylancl.mm"
include "anim12d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqtr2.mm"
include "prcom.mm"
include "eqeq2i.mm"
include "preqr1.mm"
include "sylbi.mm"
include "ex.mm"
include "syl6bi.mm"
include "impd.mm"
include "com12.mm"
include "necon3d.mm"
include "adantr.mm"
include "simpl.mm"
include "adantl.mm"
include "simprr.mm"
include "3jca.mm"
include "jctild.mm"
include "com23.mm"
include "mpdd.mm"
include "syl5bi.mm"
include "neeq2d.mm"
include "oveq2.mm"
include "fzo0to2pr.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "feq2d.mm"
include "imbi1d.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "com24.mm"
include "3impd.mm"
include "sylbid.mm"
include "imp31.mm"

theorem usgr2wlkneq
  let cP: class P
  let cF: class F
  let cG: class G
  let vk: setvar k


  assert |- ( ( ( G e. USGraph /\ F ( Walks ` G ) P ) /\ ( ( # ` F ) = 2 /\ ( P ` 0 ) =/= ( P ` ( # ` F ) ) ) ) -> ( ( ( P ` 0 ) =/= ( P ` 1 ) /\ ( P ` 0 ) =/= ( P ` 2 ) /\ ( P ` 1 ) =/= ( P ` 2 ) ) /\ ( F ` 0 ) =/= ( F ` 1 ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    chash
    cfv
    #
    c2
    wceq
    #
    cc0
    cP
    cfv
    #
    @2
    cP
    cfv
    #
    wne
    #
    wa
    #
    @4
    c1
    cP
    cfv
    #
    wne
    #
    @4
    c2
    cP
    cfv
    #
    wne
    #
    @8
    @10
    wne
    #
    w3a
    #
    cc0
    cF
    cfv
    #
    c1
    cF
    cfv
    #
    wne
    #
    wa
    #
    @0
    @1
    cF
    cG
    ciedg
    cfv
    #
    cdm
    cword
    wcel
    #
    cc0
    @2
    cfz
    co
    #
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    vk
    cv
    #
    cF
    cfv
    @18
    cfv
    @23
    cP
    cfv
    @23
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    #
    vk
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @7
    @17
    wi
    #
    @0
    cG
    cupgr
    wcel
    @1
    @27
    wb
    cG
    usgrupgr
    cP
    vk
    cF
    cG
    @18
    @21
    @21
    eqid
    @18
    eqid
    #
    upgriswlk
    syl
    @0
    @19
    @22
    @26
    @28
    @0
    @19
    @22
    @26
    @28
    wi
    wi
    @0
    @19
    wa
    #
    @7
    @26
    @22
    @17
    @30
    @3
    @6
    @26
    @22
    @17
    wi
    #
    wi
    #
    @30
    @6
    @32
    wi
    @3
    @11
    @24
    vk
    cc0
    c1
    cpr
    #
    wral
    #
    cc0
    c2
    cfz
    co
    #
    @21
    cP
    wf
    #
    @17
    wi
    #
    wi
    #
    wi
    @30
    @11
    @38
    @30
    @11
    wa
    #
    @36
    @34
    @17
    @39
    @36
    @34
    @17
    wi
    @34
    @14
    @18
    cfv
    #
    @4
    @8
    cpr
    #
    wceq
    #
    @15
    @18
    cfv
    #
    @8
    @10
    cpr
    #
    wceq
    #
    wa
    #
    @39
    @36
    wa
    #
    @17
    cP
    vk
    @18
    cF
    2wlklem
    @47
    @46
    @9
    @12
    wa
    #
    @17
    @47
    @42
    @9
    @45
    @12
    @47
    @0
    @4
    cvv
    wcel
    @42
    @9
    wi
    @0
    @19
    @11
    @36
    simplll
    #
    cc0
    cP
    fvex
    #
    @18
    cG
    @4
    @8
    cvv
    @14
    @29
    usgrnloopv
    sylancl
    @47
    @0
    @8
    cvv
    wcel
    @45
    @12
    wi
    @49
    c1
    cP
    fvex
    @18
    cG
    @8
    @10
    cvv
    @15
    @29
    usgrnloopv
    sylancl
    anim12d
    @39
    @46
    @48
    @17
    wi
    wi
    #
    @36
    @11
    @51
    @30
    @11
    @48
    @46
    @17
    @11
    @48
    @46
    @17
    wi
    @11
    @48
    wa
    #
    @46
    @16
    @13
    @11
    @46
    @16
    wi
    @48
    @46
    @11
    @16
    @46
    @14
    @15
    @4
    @10
    @14
    @15
    wceq
    #
    @46
    @4
    @10
    wceq
    #
    @53
    @42
    @45
    @54
    @53
    @42
    @43
    @41
    wceq
    #
    @45
    @54
    wi
    @53
    @40
    @43
    @41
    @14
    @15
    @18
    fveq2
    eqeq1d
    @55
    @45
    @54
    @55
    @45
    wa
    @41
    @44
    wceq
    #
    @54
    @43
    @41
    @44
    eqtr2
    @56
    @41
    @10
    @8
    cpr
    #
    wceq
    @54
    @44
    @57
    @41
    @8
    @10
    prcom
    eqeq2i
    @4
    @10
    @8
    @50
    c2
    cP
    fvex
    preqr1
    sylbi
    syl
    ex
    syl6bi
    impd
    com12
    necon3d
    com12
    adantr
    @52
    @9
    @11
    @12
    @48
    @9
    @11
    @9
    @12
    simpl
    adantl
    @11
    @48
    simpl
    @11
    @9
    @12
    simprr
    3jca
    jctild
    ex
    com23
    adantl
    adantr
    mpdd
    syl5bi
    ex
    com23
    ex
    @3
    @6
    @11
    @32
    @38
    @3
    @5
    @10
    @4
    @2
    c2
    cP
    fveq2
    neeq2d
    @3
    @26
    @34
    @31
    @37
    @3
    @24
    vk
    @25
    @33
    @3
    @25
    cc0
    c2
    cfzo
    co
    @33
    @2
    c2
    cc0
    cfzo
    oveq2
    fzo0to2pr
    syl6eq
    raleqdv
    @3
    @22
    @36
    @17
    @3
    @20
    @35
    @21
    cP
    @2
    c2
    cc0
    cfz
    oveq2
    feq2d
    imbi1d
    imbi12d
    imbi12d
    syl5ibrcom
    impd
    com24
    ex
    3impd
    sylbid
    imp31
end
