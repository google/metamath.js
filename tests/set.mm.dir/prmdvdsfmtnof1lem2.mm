include "cfmtno.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "cprime.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "wi.mm"
include "fmtnorn.mm"
include "wa.mm"
include "2a1.mm"
include "2a1d.mm"
include "wn.mm"
include "cn.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "fmtnonn.mm"
include "ad2antrl.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "ad2antll.mm"
include "mpbid.mm"
include "wne.mm"
include "simpll.mm"
include "simplr.mm"
include "weq.mm"
include "fveq2.mm"
include "con3i.mm"
include "adantl.mm"
include "neqned.mm"
include "goldbachth.mm"
include "syl3anc.mm"
include "ex.mm"
include "eqeq12.mm"
include "notbid.mm"
include "oveq12.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "ancoms.mm"
include "syl5ibcom.mm"
include "com23.mm"
include "impcom.mm"
include "imp.mm"
include "prmnn.mm"
include "coprmdvds1.mm"
include "syl3anr1.mm"
include "1nprm.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "com12.mm"
include "a1d.mm"
include "3ad2ant1.mm"
include "mpd.mm"
include "exp43.mm"
include "pm2.61i.mm"
include "rexlimdva.mm"
include "rexlimiv.mm"
include "syl2anb.mm"

theorem prmdvdsfmtnof1lem2
  let cF: class F
  let cG: class G
  let cI: class I
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F e. ran FermatNo /\ G e. ran FermatNo ) -> ( ( I e. Prime /\ I || F /\ I || G ) -> F = G ) )

  proof
    cF
    cfmtno
    crn
    #
    wcel
    vn
    cv
    #
    cfmtno
    cfv
    #
    cF
    wceq
    #
    vn
    cn0
    wrex
    #
    vm
    cv
    #
    cfmtno
    cfv
    #
    cG
    wceq
    #
    vm
    cn0
    wrex
    #
    cI
    cprime
    wcel
    #
    cI
    cF
    cdvds
    wbr
    #
    cI
    cG
    cdvds
    wbr
    #
    w3a
    #
    cF
    cG
    wceq
    #
    wi
    #
    cG
    @0
    wcel
    vn
    cF
    fmtnorn
    vm
    cG
    fmtnorn
    @4
    @8
    @14
    @3
    @8
    @14
    wi
    vn
    cn0
    @1
    cn0
    wcel
    #
    @8
    @3
    @14
    @15
    @7
    @3
    @14
    wi
    #
    vm
    cn0
    @13
    @15
    @5
    cn0
    wcel
    #
    wa
    #
    @7
    @16
    wi
    wi
    @13
    @16
    @18
    @7
    @13
    @3
    @12
    2a1
    2a1d
    @13
    wn
    #
    @18
    @7
    @3
    @14
    @19
    @18
    wa
    #
    @7
    @3
    wa
    #
    wa
    #
    cF
    cn
    wcel
    #
    cG
    cn
    wcel
    #
    cF
    cG
    cgcd
    co
    #
    c1
    wceq
    #
    @14
    @22
    @2
    cn
    wcel
    #
    @23
    @20
    @27
    @21
    @15
    @27
    @19
    @17
    @1
    fmtnonn
    ad2antrl
    adantr
    @3
    @27
    @23
    wb
    @20
    @7
    @2
    cF
    cn
    eleq1
    ad2antll
    mpbid
    @22
    @6
    cn
    wcel
    #
    @24
    @20
    @28
    @21
    @17
    @28
    @19
    @15
    @5
    fmtnonn
    ad2antll
    adantr
    @7
    @28
    @24
    wb
    @20
    @3
    @6
    cG
    cn
    eleq1
    ad2antrl
    mpbid
    @20
    @21
    @26
    @18
    @19
    @21
    @26
    wi
    @18
    @21
    @19
    @26
    @18
    @2
    @6
    wceq
    #
    wn
    #
    @2
    @6
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    #
    @21
    @19
    @26
    wi
    #
    @18
    @30
    @32
    @18
    @30
    wa
    #
    @15
    @17
    @1
    @5
    wne
    @32
    @15
    @17
    @30
    simpll
    @15
    @17
    @30
    simplr
    @35
    @1
    @5
    @30
    vn
    vm
    weq
    #
    wn
    @18
    @36
    @29
    @1
    @5
    cfmtno
    fveq2
    con3i
    adantl
    neqned
    @5
    @1
    goldbachth
    syl3anc
    ex
    @3
    @7
    @33
    @34
    wb
    @3
    @7
    wa
    #
    @30
    @19
    @32
    @26
    @37
    @29
    @13
    @2
    cF
    @6
    cG
    eqeq12
    notbid
    @37
    @31
    @25
    c1
    @2
    cF
    @6
    cG
    cgcd
    oveq12
    eqeq1d
    imbi12d
    ancoms
    syl5ibcom
    com23
    impcom
    imp
    @23
    @24
    @26
    w3a
    #
    @12
    @13
    @38
    @12
    wa
    cI
    c1
    wceq
    #
    @13
    @9
    cI
    cn
    wcel
    #
    @38
    @10
    @11
    @39
    cI
    prmnn
    @38
    @40
    @10
    @11
    w3a
    @39
    cF
    cG
    cI
    coprmdvds1
    imp
    syl3anr1
    @12
    @38
    @39
    @13
    wi
    #
    @9
    @10
    @38
    @41
    wi
    @11
    @9
    @41
    @38
    @39
    @9
    @13
    @39
    @9
    c1
    cprime
    wcel
    #
    @13
    cI
    c1
    cprime
    eleq1
    @42
    @13
    1nprm
    pm2.21i
    syl6bi
    com12
    a1d
    3ad2ant1
    impcom
    mpd
    ex
    syl3anc
    exp43
    pm2.61i
    rexlimdva
    com23
    rexlimiv
    imp
    syl2anb
end
