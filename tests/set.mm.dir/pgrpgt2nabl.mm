include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cgrp.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "wn.mm"
include "cabl.mm"
include "wnel.mm"
include "wne.mm"
include "wrex.mm"
include "ccom.mm"
include "cpmtr.mm"
include "crn.mm"
include "wss.mm"
include "eqid.mm"
include "symgtrf.mm"
include "c3.mm"
include "cle.mm"
include "cfn.mm"
include "wi.mm"
include "cn0.mm"
include "hashcl.mm"
include "c1.mm"
include "caddc.mm"
include "wb.mm"
include "2nn0.mm"
include "nn0ltp1le.mm"
include "mpan.mm"
include "2p1e3.mm"
include "a1i.mm"
include "breq1d.mm"
include "bitrd.mm"
include "biimpd.mm"
include "adantld.mm"
include "syl.mm"
include "cpnf.mm"
include "cxr.mm"
include "3re.mm"
include "rexri.mm"
include "pnfge.mm"
include "ax-mp.mm"
include "hashinf.mm"
include "syl5breqr.mm"
include "ex.mm"
include "adantr.mm"
include "com12.mm"
include "pm2.61i.mm"
include "pmtr3ncom.mm"
include "rexcom.mm"
include "sylibr.mm"
include "syldan.mm"
include "ssrexv.mm"
include "reximdv.mm"
include "mpsyl.mm"
include "symgov.mm"
include "adantl.mm"
include "pm3.22.mm"
include "neeq12d.mm"
include "2rexbidva.mm"
include "mpbird.mm"
include "rexnal.mm"
include "df-ne.mm"
include "bicomi.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "intnand.mm"
include "df-nel.mm"
include "ccmn.mm"
include "isabl.mm"
include "iscmn.mm"
include "anbi2i.mm"
include "bitri.mm"
include "xchbinx.mm"

theorem pgrpgt2nabl
  let cA: class A
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume pgrple2abl.g: |- G = ( SymGrp ` A )


  assert |- ( ( A e. V /\ 2 < ( # ` A ) ) -> G e/ Abel )

  proof
    cA
    cV
    wcel
    #
    c2
    cA
    chash
    cfv
    #
    clt
    wbr
    #
    wa
    #
    cG
    cgrp
    wcel
    #
    cG
    cmnd
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @7
    @6
    @8
    co
    #
    wceq
    #
    vy
    cG
    cbs
    cfv
    #
    wral
    #
    vx
    @12
    wral
    #
    wa
    #
    wa
    #
    wn
    cG
    cabl
    wnel
    #
    @3
    @15
    @4
    @3
    @14
    @5
    @3
    @9
    @10
    wne
    #
    vy
    @12
    wrex
    #
    vx
    @12
    wrex
    #
    @14
    wn
    #
    @3
    @20
    @6
    @7
    ccom
    #
    @7
    @6
    ccom
    #
    wne
    #
    vy
    @12
    wrex
    #
    vx
    @12
    wrex
    #
    cA
    cpmtr
    cfv
    #
    crn
    #
    @12
    wss
    #
    @3
    @25
    vx
    @28
    wrex
    #
    @26
    @12
    cA
    @28
    cG
    @28
    eqid
    pgrple2abl.g
    @12
    eqid
    #
    symgtrf
    #
    @29
    @3
    @24
    vy
    @28
    wrex
    #
    vx
    @28
    wrex
    #
    @30
    @32
    @0
    @2
    c3
    @1
    cle
    wbr
    #
    @34
    cA
    cfn
    wcel
    #
    @3
    @35
    wi
    #
    @36
    @1
    cn0
    wcel
    #
    @37
    cA
    hashcl
    @38
    @2
    @35
    @0
    @38
    @2
    @35
    @38
    @2
    c2
    c1
    caddc
    co
    #
    @1
    cle
    wbr
    #
    @35
    c2
    cn0
    wcel
    @38
    @2
    @40
    wb
    2nn0
    c2
    @1
    nn0ltp1le
    mpan
    @38
    @39
    c3
    @1
    cle
    @39
    c3
    wceq
    @38
    2p1e3
    a1i
    breq1d
    bitrd
    biimpd
    adantld
    syl
    @3
    @36
    wn
    #
    @35
    @0
    @41
    @35
    wi
    @2
    @0
    @41
    @35
    @0
    @41
    wa
    c3
    cpnf
    @1
    cle
    c3
    cxr
    wcel
    c3
    cpnf
    cle
    wbr
    c3
    3re
    rexri
    c3
    pnfge
    ax-mp
    cA
    cV
    hashinf
    syl5breqr
    ex
    adantr
    com12
    pm2.61i
    @0
    @35
    wa
    @24
    vx
    @28
    wrex
    vy
    @28
    wrex
    @34
    cA
    @27
    vy
    vx
    cV
    @27
    eqid
    pmtr3ncom
    @24
    vx
    vy
    @28
    @28
    rexcom
    sylibr
    syldan
    @29
    @33
    @25
    vx
    @28
    @24
    vy
    @28
    @12
    ssrexv
    reximdv
    mpsyl
    @25
    vx
    @28
    @12
    ssrexv
    mpsyl
    @3
    @18
    @24
    vx
    vy
    @12
    @12
    @3
    @6
    @12
    wcel
    #
    @7
    @12
    wcel
    #
    wa
    #
    wa
    #
    @9
    @22
    @10
    @23
    @44
    @9
    @22
    wceq
    @3
    cA
    @12
    @8
    cG
    @6
    @7
    pgrple2abl.g
    @31
    @8
    eqid
    #
    symgov
    adantl
    @45
    @43
    @42
    wa
    #
    @10
    @23
    wceq
    @44
    @47
    @3
    @42
    @43
    pm3.22
    adantl
    cA
    @12
    @8
    cG
    @7
    @6
    pgrple2abl.g
    @31
    @46
    symgov
    syl
    neeq12d
    2rexbidva
    mpbird
    @21
    @13
    wn
    #
    vx
    @12
    wrex
    @20
    @13
    vx
    @12
    rexnal
    @48
    @19
    vx
    @12
    @48
    @11
    wn
    #
    vy
    @12
    wrex
    @19
    @11
    vy
    @12
    rexnal
    @49
    @18
    vy
    @12
    @18
    @49
    @9
    @10
    df-ne
    bicomi
    rexbii
    bitr3i
    rexbii
    bitr3i
    sylibr
    intnand
    intnand
    @17
    cG
    cabl
    wcel
    #
    @16
    cG
    cabl
    df-nel
    @50
    @4
    cG
    ccmn
    wcel
    #
    wa
    @16
    cG
    isabl
    @51
    @15
    @4
    vx
    vy
    @12
    @8
    cG
    @31
    @46
    iscmn
    anbi2i
    bitri
    xchbinx
    sylibr
end
