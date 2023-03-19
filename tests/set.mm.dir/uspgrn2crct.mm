include "ccrcts.mm"
include "cfv.mm"
include "wbr.mm"
include "cuspgr.mm"
include "wcel.mm"
include "chash.mm"
include "c2.mm"
include "wne.mm"
include "ctrls.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "crctprop.mm"
include "cwlks.mm"
include "ccnv.mm"
include "wfun.mm"
include "istrl.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "upgriswlk.mm"
include "wb.mm"
include "preq2.mm"
include "prcom.mm"
include "syl6eq.mm"
include "eqcoms.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "ad2antrr.mm"
include "eqtr3.mm"
include "cle.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "uspgrf.mm"
include "adantl.mm"
include "adantr.mm"
include "df-f1.mm"
include "simplbi2.mm"
include "wrdf.mm"
include "syl11.mm"
include "imp.mm"
include "cn.mm"
include "2nn.mm"
include "lbfzo0.mm"
include "mpbir.mm"
include "cn0.mm"
include "clt.mm"
include "1nn0.mm"
include "1lt2.mm"
include "elfzo0.mm"
include "mpbir3an.mm"
include "pm3.2i.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "mpbiri.mm"
include "f1cofveqaeq.mm"
include "syl21anc.mm"
include "0ne1.mm"
include "eqneqall.mm"
include "syl6mpi.mm"
include "adantll.mm"
include "syl5.mm"
include "sylbid.mm"
include "expimpd.mm"
include "ex.mm"
include "2a1.mm"
include "pm2.61ine.mm"
include "fzo0to2pr.mm"
include "raleqdv.mm"
include "2wlklem.mm"
include "syl6bb.mm"
include "fveq2.mm"
include "neeq2d.mm"
include "imbi12d.mm"
include "mpbird.mm"
include "com13.mm"
include "expd.mm"
include "3adant2.mm"
include "syl6bi.mm"
include "impd.mm"
include "com23.mm"
include "mpcom.mm"
include "com12.mm"
include "sylbi.mm"
include "necon2d.mm"
include "impancom.mm"
include "syl.mm"
include "impcom.mm"

theorem uspgrn2crct
  let cP: class P
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( G e. USPGraph /\ F ( Circuits ` G ) P ) -> ( # ` F ) =/= 2 )

  proof
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    #
    cG
    cuspgr
    wcel
    #
    cF
    chash
    cfv
    #
    c2
    wne
    #
    @0
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cc0
    cP
    cfv
    #
    @2
    cP
    cfv
    #
    wceq
    #
    wa
    @1
    @3
    wi
    cP
    cF
    cG
    crctprop
    @4
    @1
    @7
    @3
    @4
    @1
    wa
    @2
    c2
    @5
    @6
    @4
    @1
    @2
    c2
    wceq
    #
    @5
    @6
    wne
    #
    wi
    #
    @4
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    ccnv
    wfun
    #
    wa
    #
    @1
    @10
    wi
    #
    cP
    cF
    cG
    istrl
    @1
    @13
    @10
    cG
    cupgr
    wcel
    #
    @1
    @13
    @10
    wi
    cG
    uspgrupgr
    @15
    @13
    @1
    @10
    @15
    @11
    @12
    @14
    @15
    @11
    cF
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
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
    cF
    cfv
    @16
    cfv
    @21
    cP
    cfv
    @21
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
    @12
    @14
    wi
    #
    cP
    vk
    cF
    cG
    @16
    @19
    @19
    eqid
    #
    @16
    eqid
    #
    upgriswlk
    @18
    @24
    @25
    @20
    @18
    @24
    wa
    #
    @12
    @1
    @10
    @8
    @12
    @1
    wa
    #
    @28
    @9
    @8
    @29
    @28
    @9
    wi
    #
    @8
    @29
    wa
    #
    @30
    @18
    cc0
    cF
    cfv
    @16
    cfv
    #
    @5
    c1
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    c1
    cF
    cfv
    @16
    cfv
    #
    @33
    c2
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    wa
    #
    wa
    #
    @5
    @37
    wne
    #
    wi
    #
    @31
    @43
    wi
    @5
    @37
    @5
    @37
    wceq
    #
    @31
    @43
    @44
    @31
    wa
    #
    @18
    @40
    @42
    @45
    @18
    wa
    #
    @40
    @35
    @36
    @34
    wceq
    #
    wa
    #
    @42
    @44
    @40
    @48
    wb
    @31
    @18
    @44
    @39
    @47
    @35
    @44
    @38
    @34
    @36
    @38
    @34
    wceq
    @37
    @5
    @37
    @5
    wceq
    @38
    @33
    @5
    cpr
    @34
    @37
    @5
    @33
    preq2
    @33
    @5
    prcom
    syl6eq
    eqcoms
    eqeq2d
    anbi2d
    ad2antrr
    @48
    @32
    @36
    wceq
    #
    @46
    @42
    @32
    @36
    @34
    eqtr3
    @31
    @18
    @49
    @42
    wi
    @44
    @31
    @18
    wa
    #
    @49
    cc0
    c1
    wceq
    #
    cc0
    c1
    wne
    @42
    @50
    @17
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    vx
    @19
    cpw
    c0
    csn
    cdif
    crab
    #
    @16
    wf1
    #
    @23
    @17
    cF
    wf1
    #
    cc0
    @23
    wcel
    #
    c1
    @23
    wcel
    #
    wa
    #
    @49
    @51
    wi
    @31
    @53
    @18
    @29
    @53
    @8
    @1
    @53
    @12
    vx
    @16
    cG
    @19
    @26
    @27
    uspgrf
    adantl
    adantl
    adantr
    @31
    @18
    @54
    @29
    @18
    @54
    wi
    #
    @8
    @12
    @58
    @1
    @23
    @17
    cF
    wf
    #
    @12
    @54
    @18
    @54
    @59
    @12
    @23
    @17
    cF
    df-f1
    simplbi2
    @17
    cF
    wrdf
    syl11
    adantr
    adantl
    imp
    @8
    @57
    @29
    @18
    @8
    @57
    cc0
    cc0
    c2
    cfzo
    co
    #
    wcel
    #
    c1
    @60
    wcel
    #
    wa
    @61
    @62
    @61
    c2
    cn
    wcel
    #
    2nn
    c2
    lbfzo0
    mpbir
    @62
    c1
    cn0
    wcel
    @63
    c1
    c2
    clt
    wbr
    1nn0
    2nn
    1lt2
    c1
    c2
    elfzo0
    mpbir3an
    pm3.2i
    @8
    @55
    @61
    @56
    @62
    @8
    @23
    @60
    cc0
    @2
    c2
    cc0
    cfzo
    oveq2
    #
    eleq2d
    @8
    @23
    @60
    c1
    @64
    eleq2d
    anbi12d
    mpbiri
    ad2antrr
    @23
    @17
    @52
    @16
    cF
    cc0
    c1
    f1cofveqaeq
    syl21anc
    0ne1
    @42
    cc0
    c1
    eqneqall
    syl6mpi
    adantll
    syl5
    sylbid
    expimpd
    ex
    @42
    @31
    @41
    2a1
    pm2.61ine
    @8
    @30
    @43
    wb
    @29
    @8
    @28
    @41
    @9
    @42
    @8
    @24
    @40
    @18
    @8
    @24
    @22
    vk
    cc0
    c1
    cpr
    #
    wral
    @40
    @8
    @22
    vk
    @23
    @65
    @8
    @23
    @60
    @65
    @64
    fzo0to2pr
    syl6eq
    raleqdv
    cP
    vk
    @16
    cF
    2wlklem
    syl6bb
    anbi2d
    @8
    @6
    @37
    @5
    @2
    c2
    cP
    fveq2
    neeq2d
    imbi12d
    adantr
    mpbird
    ex
    com13
    expd
    3adant2
    syl6bi
    impd
    com23
    mpcom
    com12
    sylbi
    imp
    necon2d
    impancom
    syl
    impcom
end
