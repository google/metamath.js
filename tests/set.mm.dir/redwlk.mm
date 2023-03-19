include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "c1.mm"
include "chash.mm"
include "cle.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "cres.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wi.mm"
include "wlkv.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "wral.mm"
include "eqid.mm"
include "iswlk.mm"
include "wrdred1.mm"
include "a1i.mm"
include "wlkf.mm"
include "redwlklem.mm"
include "3exp.mm"
include "syl.mm"
include "imp.mm"
include "cn0.mm"
include "wlkcl.mm"
include "wrdred1hash.mm"
include "sylan.mm"
include "cz.mm"
include "nn0z.mm"
include "fzossrbm1.mm"
include "ssralv.mm"
include "sselda.mm"
include "fvres.mm"
include "eqcomd.mm"
include "fzo0ss1.mm"
include "simpr.mm"
include "adantr.mm"
include "1zzd.mm"
include "fzoaddel2.mm"
include "syl3anc.mm"
include "sseldi.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "preq12d.mm"
include "sseq12d.mm"
include "ifpbi123d.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "syld.mm"
include "wb.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "sylibd.mm"
include "syl2an2r.mm"
include "3anim123d.mm"
include "id.mm"
include "resexg.mm"
include "bicomd.mm"
include "syl3an.mm"
include "syl5ib.mm"
include "expcomd.mm"
include "sylbid.mm"
include "mpcom.mm"
include "anabsi5.mm"

theorem redwlk
  let cP: class P
  let cF: class F
  let cG: class G
  let vk: setvar k


  assert |- ( ( F ( Walks ` G ) P /\ 1 <_ ( # ` F ) ) -> ( F |` ( 0 ..^ ( ( # ` F ) - 1 ) ) ) ( Walks ` G ) ( P |` ( 0 ..^ ( # ` F ) ) ) )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    #
    wbr
    #
    c1
    cF
    chash
    cfv
    #
    cle
    wbr
    #
    cF
    cc0
    @2
    c1
    cmin
    co
    #
    cfzo
    co
    #
    cres
    #
    cP
    cc0
    @2
    cfzo
    co
    #
    cres
    #
    @0
    wbr
    #
    cG
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    w3a
    #
    @1
    @1
    @3
    wa
    #
    @9
    wi
    #
    cP
    cF
    cG
    wlkv
    @13
    @1
    cF
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    #
    wcel
    #
    cc0
    @2
    cfz
    co
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
    cP
    cfv
    #
    @22
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    #
    @22
    cF
    cfv
    #
    @16
    cfv
    #
    @23
    csn
    #
    wceq
    #
    @23
    @25
    cpr
    #
    @28
    wss
    #
    wif
    #
    vk
    @7
    wral
    #
    w3a
    #
    @15
    cP
    cvv
    vk
    cF
    cG
    @16
    @20
    cvv
    cvv
    @20
    eqid
    #
    @16
    eqid
    #
    iswlk
    @13
    @14
    @35
    @9
    @14
    @35
    wa
    @6
    @18
    wcel
    #
    cc0
    @6
    chash
    cfv
    #
    cfz
    co
    @20
    @8
    wf
    #
    @22
    @8
    cfv
    #
    @24
    @8
    cfv
    #
    wceq
    #
    @22
    @6
    cfv
    #
    @16
    cfv
    #
    @41
    csn
    #
    wceq
    #
    @41
    @42
    cpr
    #
    @45
    wss
    #
    wif
    #
    vk
    cc0
    @39
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @13
    @9
    @14
    @35
    @53
    @14
    @19
    @38
    @21
    @40
    @34
    @52
    @19
    @38
    wi
    @14
    @17
    cF
    wrdred1
    a1i
    @1
    @3
    @21
    @40
    wi
    #
    @1
    @19
    @3
    @54
    wi
    cP
    cF
    cG
    @16
    @37
    wlkf
    #
    @19
    @3
    @21
    @40
    cP
    @17
    cF
    @20
    redwlklem
    3exp
    syl
    imp
    @1
    @2
    cn0
    wcel
    #
    @3
    @39
    @4
    wceq
    #
    @34
    @52
    wi
    cP
    cF
    cG
    wlkcl
    @1
    @19
    @3
    @57
    @55
    @17
    cF
    wrdred1hash
    sylan
    @56
    @57
    wa
    @34
    @50
    vk
    @5
    wral
    #
    @52
    @56
    @34
    @58
    wi
    @57
    @56
    @34
    @33
    vk
    @5
    wral
    #
    @58
    @56
    @5
    @7
    wss
    #
    @34
    @59
    wi
    @56
    @2
    cz
    wcel
    #
    @60
    @2
    nn0z
    #
    @2
    fzossrbm1
    syl
    #
    @33
    vk
    @5
    @7
    ssralv
    syl
    @56
    @33
    @50
    vk
    @5
    @56
    @22
    @5
    wcel
    #
    wa
    #
    @33
    @50
    @65
    @26
    @30
    @32
    @43
    @47
    @49
    @65
    @23
    @41
    @25
    @42
    @65
    @41
    @23
    @65
    @22
    @7
    wcel
    @41
    @23
    wceq
    @56
    @5
    @7
    @22
    @63
    sselda
    @22
    @7
    cP
    fvres
    syl
    eqcomd
    #
    @65
    @42
    @25
    @65
    @24
    @7
    wcel
    @42
    @25
    wceq
    @65
    c1
    @2
    cfzo
    co
    #
    @7
    @24
    @2
    fzo0ss1
    @65
    @64
    @61
    c1
    cz
    wcel
    @24
    @67
    wcel
    @56
    @64
    simpr
    @56
    @61
    @64
    @62
    adantr
    @65
    1zzd
    @22
    @2
    c1
    fzoaddel2
    syl3anc
    sseldi
    @24
    @7
    cP
    fvres
    syl
    eqcomd
    #
    eqeq12d
    @65
    @28
    @45
    @29
    @46
    @65
    @27
    @44
    @16
    @65
    @44
    @27
    @64
    @44
    @27
    wceq
    @56
    @22
    @5
    cF
    fvres
    adantl
    eqcomd
    fveq2d
    #
    @65
    @23
    @41
    @66
    sneqd
    eqeq12d
    @65
    @31
    @48
    @28
    @45
    @65
    @23
    @41
    @25
    @42
    @66
    @68
    preq12d
    @69
    sseq12d
    ifpbi123d
    biimpd
    ralimdva
    syld
    adantr
    @57
    @58
    @52
    wb
    @56
    @57
    @50
    vk
    @5
    @51
    @57
    @51
    @5
    @39
    @4
    cc0
    cfzo
    oveq2
    eqcomd
    raleqdv
    adantl
    sylibd
    syl2an2r
    3anim123d
    imp
    @10
    @10
    @11
    @6
    cvv
    wcel
    #
    @12
    @8
    cvv
    wcel
    #
    @53
    @9
    wb
    @10
    id
    cF
    @5
    cvv
    resexg
    cP
    @7
    cvv
    resexg
    @10
    @70
    @71
    w3a
    @9
    @53
    @8
    cvv
    vk
    @6
    cG
    @16
    @20
    cvv
    cvv
    @36
    @37
    iswlk
    bicomd
    syl3an
    syl5ib
    expcomd
    sylbid
    mpcom
    anabsi5
end
