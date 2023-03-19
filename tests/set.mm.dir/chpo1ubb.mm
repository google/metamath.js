include "cv.mm"
include "cchp.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "wral.mm"
include "wrex.mm"
include "cmul.mm"
include "wtru.mm"
include "c1.mm"
include "c2.mm"
include "cr.mm"
include "wss.mm"
include "rpssre.mm"
include "a1i.mm"
include "1red.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "rpred.mm"
include "chpcl.mm"
include "syl.mm"
include "rerpdivcld.mm"
include "cmpt.mm"
include "co1.mm"
include "chpo1ub.mm"
include "o1lo1d.mm"
include "ad2antrl.mm"
include "rehalfcld.mm"
include "clt.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "adantr.mm"
include "chpeq0.mm"
include "biimpar.mm"
include "oveq1d.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "div0d.mm"
include "ad2ant2r.mm"
include "2rp.mm"
include "simprll.mm"
include "chpge0.mm"
include "divge0d.mm"
include "eqbrtrd.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "ltled.mm"
include "chpwordi.mm"
include "syl3anc.mm"
include "lediv12ad.mm"
include "2re.mm"
include "ltlecasei.mm"
include "lo1bddrp.mm"
include "trud.mm"
include "simpl.mm"
include "ledivmul2d.mm"
include "ralbidva.mm"
include "rexbiia.mm"
include "mpbi.mm"

theorem chpo1ubb
  let vx: setvar x
  let vc: setvar c
  let vn: setvar n
  let vy: setvar y

  disjoint c x
  disjoint c n
  disjoint c y
  disjoint n x
  disjoint n y
  disjoint x y
  assert |- E. c e. RR+ A. x e. RR+ ( psi ` x ) <_ ( c x. x )

  proof
    vx
    cv
    #
    cchp
    cfv
    #
    @0
    cdiv
    co
    #
    vc
    cv
    #
    cle
    wbr
    #
    vx
    crp
    wral
    #
    vc
    crp
    wrex
    #
    @1
    @3
    @0
    cmul
    co
    cle
    wbr
    #
    vx
    crp
    wral
    #
    vc
    crp
    wrex
    @6
    wtru
    vx
    vy
    crp
    @2
    c1
    vc
    vy
    cv
    #
    cchp
    cfv
    #
    c2
    cdiv
    co
    #
    crp
    cr
    wss
    wtru
    rpssre
    a1i
    wtru
    1red
    wtru
    @0
    crp
    wcel
    #
    wa
    #
    @1
    @0
    @13
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @13
    @0
    wtru
    @12
    simpr
    #
    rpred
    #
    @0
    chpcl
    #
    syl
    #
    @16
    rerpdivcld
    #
    wtru
    vx
    crp
    @2
    @20
    vx
    crp
    @2
    cmpt
    co1
    wcel
    wtru
    vx
    chpo1ub
    a1i
    o1lo1d
    wtru
    @9
    cr
    wcel
    #
    c1
    @9
    cle
    wbr
    #
    wa
    #
    wa
    @10
    @21
    @10
    cr
    wcel
    #
    wtru
    @22
    @9
    chpcl
    ad2antrl
    #
    rehalfcld
    @13
    @23
    @0
    @9
    clt
    wbr
    #
    wa
    #
    wa
    #
    @2
    @11
    cle
    wbr
    @0
    c2
    @28
    @0
    c2
    clt
    wbr
    #
    wa
    #
    @2
    cc0
    @0
    cdiv
    co
    #
    @11
    cle
    @30
    @1
    cc0
    @0
    cdiv
    @28
    @1
    cc0
    wceq
    #
    @29
    @28
    @14
    @32
    @29
    wb
    @13
    @14
    @27
    @17
    adantr
    #
    @0
    chpeq0
    syl
    biimpar
    oveq1d
    @28
    @31
    @11
    cle
    wbr
    @29
    @28
    @31
    cc0
    @11
    cle
    @28
    @0
    @28
    @0
    @13
    @12
    @27
    @16
    adantr
    #
    rpcnd
    @28
    @0
    @34
    rpne0d
    div0d
    @28
    @10
    c2
    wtru
    @23
    @24
    @12
    @26
    @25
    ad2ant2r
    #
    c2
    crp
    wcel
    #
    @28
    2rp
    a1i
    @28
    @21
    cc0
    @10
    cle
    wbr
    @13
    @21
    @22
    @26
    simprll
    #
    @9
    chpge0
    syl
    divge0d
    eqbrtrd
    adantr
    eqbrtrd
    @28
    c2
    @0
    cle
    wbr
    #
    wa
    #
    @1
    @10
    c2
    @0
    @13
    @15
    @27
    @38
    @19
    ad2antrr
    @28
    @24
    @38
    @35
    adantr
    @36
    @39
    2rp
    a1i
    @28
    @14
    @38
    @33
    adantr
    #
    @39
    @14
    cc0
    @1
    cle
    wbr
    @40
    @0
    chpge0
    syl
    @39
    @14
    @21
    @0
    @9
    cle
    wbr
    #
    @1
    @10
    cle
    wbr
    @40
    @28
    @21
    @38
    @37
    adantr
    @28
    @41
    @38
    @28
    @0
    @9
    @33
    @37
    @13
    @23
    @26
    simprr
    ltled
    adantr
    @0
    @9
    chpwordi
    syl3anc
    @28
    @38
    simpr
    lediv12ad
    @33
    c2
    cr
    wcel
    @28
    2re
    a1i
    ltlecasei
    lo1bddrp
    trud
    @5
    @8
    vc
    crp
    @3
    crp
    wcel
    #
    @4
    @7
    vx
    crp
    @42
    @12
    wa
    #
    @1
    @3
    @0
    @43
    @14
    @15
    @43
    @0
    @42
    @12
    simpr
    #
    rpred
    @18
    syl
    @43
    @3
    @42
    @12
    simpl
    rpred
    @44
    ledivmul2d
    ralbidva
    rexbiia
    mpbi
end
