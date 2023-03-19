include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cn.mm"
include "cpw.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "cr.mm"
include "cvv.mm"
include "wss.mm"
include "reex.mm"
include "cuni.mm"
include "elssuni.mm"
include "uniretop.mm"
include "syl6sseqr.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "rpnnen.mm"
include "domentr.mm"
include "sylancl.mm"
include "adantr.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cbl.mm"
include "co.mm"
include "crp.mm"
include "sselda.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "cicc.mm"
include "cc0.mm"
include "c1.mm"
include "rpnnen2.mm"
include "clt.mm"
include "rphalfcl.mm"
include "rpred.mm"
include "resubcl.mm"
include "sylan2.mm"
include "readdcl.mm"
include "simpl.mm"
include "ltsubrp.mm"
include "ltaddrp.mm"
include "lttrd.mm"
include "iccen.mm"
include "syl3anc.mm"
include "sylancr.mm"
include "ovex.mm"
include "cxr.mm"
include "rpre.mm"
include "rexrd.mm"
include "recnd.mm"
include "adantl.mm"
include "subsub4d.mm"
include "2halvesd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "ltsubrpd.mm"
include "eqbrtrrd.mm"
include "syl2anc.mm"
include "addassd.mm"
include "breqtrd.mm"
include "iccssioo.mm"
include "syl22anc.mm"
include "domtr.mm"
include "wceq.mm"
include "eqid.mm"
include "bl2ioo.mm"
include "breqtrrd.mm"
include "sylan.mm"
include "simplll.mm"
include "simpr.mm"
include "sylc.mm"
include "cmopn.mm"
include "wrex.mm"
include "tgioo.mm"
include "eleq2i.mm"
include "cxmt.mm"
include "rexmet.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "sylanb.mm"
include "r19.29a.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "sbth.mm"

theorem opnreen
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( A e. ( topGen ` ran (,) ) /\ A =/= (/) ) -> A ~~ ~P NN )

  proof
    cA
    cioo
    crn
    ctg
    cfv
    #
    wcel
    #
    cA
    c0
    wne
    #
    wa
    cA
    cn
    cpw
    #
    cdom
    wbr
    #
    @3
    cA
    cdom
    wbr
    #
    cA
    @3
    cen
    wbr
    @1
    @4
    @2
    @1
    cA
    cr
    cdom
    wbr
    #
    cr
    @3
    cen
    wbr
    @4
    cr
    cvv
    wcel
    @1
    cA
    cr
    wss
    @6
    reex
    @1
    cA
    @0
    cuni
    cr
    cA
    @0
    elssuni
    uniretop
    syl6sseqr
    #
    cA
    cr
    cvv
    ssdomg
    mpsyl
    rpnnen
    cA
    cr
    @3
    domentr
    sylancl
    adantr
    @1
    @2
    @5
    @2
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    @1
    @5
    vx
    cA
    n0
    @1
    @9
    @5
    vx
    @1
    @9
    @5
    @1
    @9
    wa
    #
    @8
    vy
    cv
    #
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    cbl
    cfv
    co
    #
    cA
    wss
    #
    @5
    vy
    crp
    @10
    @11
    crp
    wcel
    #
    wa
    #
    @14
    wa
    #
    @3
    @13
    cdom
    wbr
    #
    @13
    cA
    cdom
    wbr
    #
    @5
    @16
    @18
    @14
    @10
    @8
    cr
    wcel
    #
    @15
    @18
    @1
    cA
    cr
    @8
    @7
    sselda
    @20
    @15
    wa
    #
    @3
    @8
    @11
    cmin
    co
    #
    @8
    @11
    caddc
    co
    #
    cioo
    co
    #
    @13
    cdom
    @21
    @3
    @8
    @11
    c2
    cdiv
    co
    #
    cmin
    co
    #
    @8
    @25
    caddc
    co
    #
    cicc
    co
    #
    cdom
    wbr
    #
    @28
    @24
    cdom
    wbr
    #
    @3
    @24
    cdom
    wbr
    @21
    @3
    cc0
    c1
    cicc
    co
    #
    cdom
    wbr
    @31
    @28
    cen
    wbr
    #
    @29
    rpnnen2
    @21
    @26
    cr
    wcel
    #
    @27
    cr
    wcel
    #
    @26
    @27
    clt
    wbr
    @32
    @15
    @20
    @25
    cr
    wcel
    #
    @33
    @15
    @25
    @11
    rphalfcl
    #
    rpred
    #
    @8
    @25
    resubcl
    sylan2
    #
    @15
    @20
    @35
    @34
    @37
    @8
    @25
    readdcl
    sylan2
    #
    @21
    @26
    @8
    @27
    @38
    @20
    @15
    simpl
    #
    @39
    @15
    @20
    @25
    crp
    wcel
    #
    @26
    @8
    clt
    wbr
    @36
    @8
    @25
    ltsubrp
    sylan2
    @15
    @20
    @41
    @8
    @27
    clt
    wbr
    @36
    @8
    @25
    ltaddrp
    sylan2
    lttrd
    @26
    @27
    iccen
    syl3anc
    @3
    @31
    @28
    domentr
    sylancr
    @24
    cvv
    wcel
    @21
    @28
    @24
    wss
    #
    @30
    @22
    @23
    cioo
    ovex
    @21
    @22
    cxr
    wcel
    @23
    cxr
    wcel
    @22
    @26
    clt
    wbr
    @27
    @23
    clt
    wbr
    @42
    @21
    @22
    @15
    @20
    @11
    cr
    wcel
    #
    @22
    cr
    wcel
    @11
    rpre
    #
    @8
    @11
    resubcl
    sylan2
    rexrd
    @21
    @23
    @15
    @20
    @43
    @23
    cr
    wcel
    @44
    @8
    @11
    readdcl
    sylan2
    rexrd
    @21
    @26
    @25
    cmin
    co
    #
    @22
    @26
    clt
    @21
    @45
    @8
    @25
    @25
    caddc
    co
    #
    cmin
    co
    @22
    @21
    @8
    @25
    @25
    @21
    @8
    @40
    recnd
    #
    @21
    @25
    @15
    @35
    @20
    @37
    adantl
    recnd
    #
    @48
    subsub4d
    @21
    @46
    @11
    @8
    cmin
    @21
    @11
    @21
    @11
    @15
    @43
    @20
    @44
    adantl
    recnd
    2halvesd
    #
    oveq2d
    eqtrd
    @21
    @26
    @25
    @38
    @15
    @41
    @20
    @36
    adantl
    #
    ltsubrpd
    eqbrtrrd
    @21
    @27
    @27
    @25
    caddc
    co
    #
    @23
    clt
    @21
    @34
    @41
    @27
    @51
    clt
    wbr
    @39
    @50
    @27
    @25
    ltaddrp
    syl2anc
    @21
    @51
    @8
    @46
    caddc
    co
    @23
    @21
    @8
    @25
    @25
    @47
    @48
    @48
    addassd
    @21
    @46
    @11
    @8
    caddc
    @49
    oveq2d
    eqtrd
    breqtrd
    @22
    @23
    @26
    @27
    iccssioo
    syl22anc
    @28
    @24
    cvv
    ssdomg
    mpsyl
    @3
    @28
    @24
    domtr
    syl2anc
    @15
    @20
    @43
    @13
    @24
    wceq
    @44
    @8
    @11
    @12
    @12
    eqid
    #
    bl2ioo
    sylan2
    breqtrrd
    sylan
    adantr
    @17
    @1
    @14
    @19
    @1
    @9
    @15
    @14
    simplll
    @16
    @14
    simpr
    @13
    cA
    @0
    ssdomg
    sylc
    @3
    @13
    cA
    domtr
    syl2anc
    @1
    cA
    @12
    cmopn
    cfv
    #
    wcel
    #
    @9
    @14
    vy
    crp
    wrex
    #
    @0
    @53
    cA
    @12
    @53
    @52
    @53
    eqid
    #
    tgioo
    eleq2i
    @12
    cr
    cxmt
    cfv
    wcel
    @54
    @9
    @55
    @12
    @52
    rexmet
    vy
    cA
    @12
    @8
    @53
    cr
    @56
    mopni2
    mp3an1
    sylanb
    r19.29a
    ex
    exlimdv
    syl5bi
    imp
    cA
    @3
    sbth
    syl2anc
end
