include "crp.mm"
include "cv.mm"
include "ccht.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "c3.mm"
include "c2.mm"
include "clog.mm"
include "cmul.mm"
include "cr.mm"
include "wss.mm"
include "rpssre.mm"
include "a1i.mm"
include "cc.mm"
include "rpre.mm"
include "chtcl.mm"
include "syl.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "recnd.mm"
include "adantl.mm"
include "3re.mm"
include "2rp.mm"
include "relogcl.mm"
include "ax-mp.mm"
include "2re.mm"
include "remulcli.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cabs.mm"
include "wceq.mm"
include "cc0.mm"
include "clt.mm"
include "chtge0.mm"
include "rpregt0.mm"
include "divge0.mm"
include "syl21anc.mm"
include "absidd.mm"
include "adantr.mm"
include "cmin.mm"
include "remulcl.mm"
include "sylancr.mm"
include "resubcl.mm"
include "sylancl.mm"
include "2lt3.mm"
include "simpr.mm"
include "ltletrd.mm"
include "chtub.mm"
include "syl2anc.mm"
include "3pos.mm"
include "elrpii.mm"
include "ltsubrp.mm"
include "wb.mm"
include "c1.mm"
include "1lt2.mm"
include "rplogcl.mm"
include "mp2an.mm"
include "elrp.mm"
include "mpbi.mm"
include "ltmul2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "lttrd.mm"
include "recni.mm"
include "2cnd.mm"
include "mulassd.mm"
include "breqtrrd.mm"
include "ltdivmul2.mm"
include "mpbird.mm"
include "ltled.mm"
include "eqbrtrd.mm"
include "elo1d.mm"
include "trud.mm"

theorem chto1ub
  let vx: setvar x


  assert |- ( x e. RR+ |-> ( ( theta ` x ) / x ) ) e. O(1)

  proof
    vx
    crp
    vx
    cv
    #
    ccht
    cfv
    #
    @0
    cdiv
    co
    #
    cmpt
    co1
    wcel
    wtru
    vx
    crp
    @2
    c3
    c2
    clog
    cfv
    #
    c2
    cmul
    co
    #
    crp
    cr
    wss
    wtru
    rpssre
    a1i
    @0
    crp
    wcel
    #
    @2
    cc
    wcel
    wtru
    @5
    @2
    @1
    cr
    wcel
    #
    @5
    @2
    cr
    wcel
    #
    @5
    @0
    cr
    wcel
    #
    @6
    @0
    rpre
    #
    @0
    chtcl
    syl
    #
    @1
    @0
    rerpdivcl
    mpancom
    #
    recnd
    adantl
    c3
    cr
    wcel
    #
    wtru
    3re
    a1i
    @4
    cr
    wcel
    #
    wtru
    @3
    c2
    c2
    crp
    wcel
    @3
    cr
    wcel
    #
    2rp
    c2
    relogcl
    ax-mp
    #
    2re
    remulcli
    #
    a1i
    @5
    c3
    @0
    cle
    wbr
    #
    wa
    #
    @2
    cabs
    cfv
    #
    @4
    cle
    wbr
    wtru
    @18
    @19
    @2
    @4
    cle
    @5
    @19
    @2
    wceq
    @17
    @5
    @2
    @11
    @5
    @6
    cc0
    @1
    cle
    wbr
    #
    @8
    cc0
    @0
    clt
    wbr
    wa
    #
    cc0
    @2
    cle
    wbr
    @10
    @5
    @8
    @20
    @9
    @0
    chtge0
    syl
    @0
    rpregt0
    #
    @1
    @0
    divge0
    syl21anc
    absidd
    adantr
    @18
    @2
    @4
    @5
    @7
    @17
    @11
    adantr
    @13
    @18
    @16
    a1i
    #
    @18
    @2
    @4
    clt
    wbr
    #
    @1
    @4
    @0
    cmul
    co
    #
    clt
    wbr
    #
    @18
    @1
    @3
    c2
    @0
    cmul
    co
    #
    cmul
    co
    #
    @25
    clt
    @18
    @1
    @3
    @27
    c3
    cmin
    co
    #
    cmul
    co
    #
    @28
    @5
    @6
    @17
    @10
    adantr
    #
    @18
    @14
    @29
    cr
    wcel
    #
    @30
    cr
    wcel
    @15
    @18
    @27
    cr
    wcel
    #
    @12
    @32
    @18
    c2
    cr
    wcel
    #
    @8
    @33
    2re
    @5
    @8
    @17
    @9
    adantr
    #
    c2
    @0
    remulcl
    sylancr
    #
    3re
    @27
    c3
    resubcl
    sylancl
    #
    @3
    @29
    remulcl
    sylancr
    @18
    @14
    @33
    @28
    cr
    wcel
    @15
    @36
    @3
    @27
    remulcl
    sylancr
    @18
    @8
    c2
    @0
    clt
    wbr
    @1
    @30
    clt
    wbr
    @35
    @18
    c2
    c3
    @0
    @34
    @18
    2re
    a1i
    @12
    @18
    3re
    a1i
    @35
    c2
    c3
    clt
    wbr
    @18
    2lt3
    a1i
    @5
    @17
    simpr
    ltletrd
    @0
    chtub
    syl2anc
    @18
    @29
    @27
    clt
    wbr
    #
    @30
    @28
    clt
    wbr
    #
    @18
    @33
    c3
    crp
    wcel
    @38
    @36
    c3
    3re
    3pos
    elrpii
    @27
    c3
    ltsubrp
    sylancl
    @18
    @32
    @33
    @14
    cc0
    @3
    clt
    wbr
    wa
    #
    @38
    @39
    wb
    @37
    @36
    @40
    @18
    @3
    crp
    wcel
    #
    @40
    @34
    c1
    c2
    clt
    wbr
    @41
    2re
    1lt2
    c2
    rplogcl
    mp2an
    @3
    elrp
    mpbi
    a1i
    @29
    @27
    @3
    ltmul2
    syl3anc
    mpbid
    lttrd
    @18
    @3
    c2
    @0
    @3
    cc
    wcel
    @18
    @3
    @15
    recni
    a1i
    @18
    2cnd
    @5
    @0
    cc
    wcel
    @17
    @5
    @0
    @9
    recnd
    adantr
    mulassd
    breqtrrd
    @18
    @6
    @13
    @21
    @24
    @26
    wb
    @31
    @23
    @5
    @21
    @17
    @22
    adantr
    @1
    @4
    @0
    ltdivmul2
    syl3anc
    mpbird
    ltled
    eqbrtrd
    adantl
    elo1d
    trud
end
