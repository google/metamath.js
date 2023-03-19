include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "cv.mm"
include "cpnf.mm"
include "cioc.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cmnf.mm"
include "cico.mm"
include "cun.mm"
include "cioo.mm"
include "ctg.mm"
include "wss.mm"
include "cr.mm"
include "wrex.mm"
include "eqid.mm"
include "leordtval.mm"
include "eleq2i.mm"
include "wa.mm"
include "tg2.mm"
include "wo.mm"
include "wi.mm"
include "elun.mm"
include "wceq.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "cc0.mm"
include "wbr.mm"
include "cif.mm"
include "clt.mm"
include "mnfxr.mm"
include "a1i.mm"
include "simprl.mm"
include "0xr.mm"
include "ifcl.mm"
include "sylancl.mm"
include "pnfxr.mm"
include "xrmax1.mm"
include "sylancr.mm"
include "ge0gtmnf.mm"
include "syl2anc.mm"
include "w3a.mm"
include "simpll.mm"
include "simprr.mm"
include "eleqtrd.mm"
include "elioc1.mm"
include "mpbid.mm"
include "simp2d.mm"
include "0ltpnf.mm"
include "breq1.mm"
include "ifboth.mm"
include "xrre2.mm"
include "syl32anc.mm"
include "xrmax2.mm"
include "df-ioc.mm"
include "xrlelttr.mm"
include "ixxss1.mm"
include "simplr.mm"
include "eqsstr3d.mm"
include "sstrd.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "rexlimdvaa.mm"
include "com12.mm"
include "sylbi.mm"
include "wn.mm"
include "pnfnlt.mm"
include "elico1.mm"
include "mpan.mm"
include "simp3.mm"
include "syl6bi.mm"
include "mtod.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "pm2.21d.mm"
include "adantrd.mm"
include "jaoi.mm"
include "pnfnre.mm"
include "neli.mm"
include "cuni.mm"
include "elssuni.mm"
include "unirnioo.mm"
include "syl6sseqr.mm"
include "sseld.mm"
include "mtoi.mm"
include "syl.mm"
include "sylanb.mm"

theorem pnfnei
  let vx: setvar x
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( A e. ( ordTop ` <_ ) /\ +oo e. A ) -> E. x e. RR ( x (,] +oo ) C_ A )

  proof
    cA
    cle
    cordt
    cfv
    #
    wcel
    cA
    vy
    cxr
    vy
    cv
    #
    cpnf
    cioc
    co
    #
    cmpt
    #
    crn
    #
    vy
    cxr
    cmnf
    @1
    cico
    co
    #
    cmpt
    #
    crn
    #
    cun
    #
    cioo
    crn
    #
    cun
    #
    ctg
    cfv
    #
    wcel
    #
    cpnf
    cA
    wcel
    #
    vx
    cv
    #
    cpnf
    cioc
    co
    #
    cA
    wss
    #
    vx
    cr
    wrex
    #
    @0
    @11
    cA
    vy
    @4
    @7
    @9
    @4
    eqid
    @7
    eqid
    @9
    eqid
    leordtval
    eleq2i
    @12
    @13
    wa
    cpnf
    vu
    cv
    #
    wcel
    #
    @18
    cA
    wss
    #
    wa
    #
    vu
    @10
    wrex
    @17
    vu
    cA
    @10
    cpnf
    tg2
    @21
    @17
    vu
    @10
    @18
    @10
    wcel
    @18
    @8
    wcel
    #
    @18
    @9
    wcel
    #
    wo
    @21
    @17
    wi
    #
    @18
    @8
    @9
    elun
    @22
    @24
    @23
    @22
    @18
    @4
    wcel
    #
    @18
    @7
    wcel
    #
    wo
    @24
    @18
    @4
    @7
    elun
    @25
    @24
    @26
    @25
    @18
    @2
    wceq
    #
    vy
    cxr
    wrex
    #
    @24
    @18
    cvv
    wcel
    #
    @25
    @28
    wb
    vu
    vex
    #
    vy
    cxr
    @2
    @18
    @3
    cvv
    @3
    eqid
    elrnmpt
    ax-mp
    @21
    @28
    @17
    @21
    @27
    @17
    vy
    cxr
    @21
    @1
    cxr
    wcel
    #
    @27
    wa
    #
    wa
    #
    cc0
    @1
    cle
    wbr
    #
    @1
    cc0
    cif
    #
    cr
    wcel
    #
    @35
    cpnf
    cioc
    co
    #
    cA
    wss
    #
    @17
    @33
    cmnf
    cxr
    wcel
    #
    @35
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cmnf
    @35
    clt
    wbr
    #
    @35
    cpnf
    clt
    wbr
    #
    @36
    @39
    @33
    mnfxr
    a1i
    @33
    @31
    cc0
    cxr
    wcel
    #
    @40
    @21
    @31
    @27
    simprl
    #
    0xr
    @34
    @1
    cc0
    cxr
    ifcl
    sylancl
    #
    @41
    @33
    pnfxr
    a1i
    @33
    @40
    cc0
    @35
    cle
    wbr
    #
    @42
    @46
    @33
    @44
    @31
    @47
    0xr
    @45
    cc0
    @1
    xrmax1
    sylancr
    @35
    ge0gtmnf
    syl2anc
    @33
    @1
    cpnf
    clt
    wbr
    #
    cc0
    cpnf
    clt
    wbr
    #
    @43
    @33
    @41
    @48
    cpnf
    cpnf
    cle
    wbr
    #
    @33
    cpnf
    @2
    wcel
    #
    @41
    @48
    @50
    w3a
    #
    @33
    cpnf
    @18
    @2
    @19
    @20
    @32
    simpll
    @21
    @31
    @27
    simprr
    #
    eleqtrd
    @33
    @31
    @41
    @51
    @52
    wb
    @45
    pnfxr
    @1
    cpnf
    cpnf
    elioc1
    sylancl
    mpbid
    simp2d
    0ltpnf
    @34
    @48
    @49
    @43
    @1
    cc0
    @1
    @35
    cpnf
    clt
    breq1
    cc0
    @35
    cpnf
    clt
    breq1
    ifboth
    sylancl
    cmnf
    @35
    cpnf
    xrre2
    syl32anc
    @33
    @37
    @2
    cA
    @33
    @31
    @1
    @35
    cle
    wbr
    #
    @37
    @2
    wss
    @45
    @33
    @44
    @31
    @54
    0xr
    @45
    cc0
    @1
    xrmax2
    sylancr
    va
    vb
    vc
    vx
    @1
    @35
    cpnf
    cioc
    clt
    cle
    clt
    cioc
    cle
    va
    vb
    vc
    df-ioc
    #
    @55
    @1
    @35
    @14
    xrlelttr
    ixxss1
    syl2anc
    @33
    @2
    @18
    cA
    @53
    @19
    @20
    @32
    simplr
    eqsstr3d
    sstrd
    @16
    @38
    vx
    @35
    cr
    @14
    @35
    wceq
    @15
    @37
    cA
    @14
    @35
    cpnf
    cioc
    oveq1
    sseq1d
    rspcev
    syl2anc
    rexlimdvaa
    com12
    sylbi
    @26
    @18
    @5
    wceq
    #
    vy
    cxr
    wrex
    #
    @24
    @29
    @26
    @57
    wb
    @30
    vy
    cxr
    @5
    @18
    @6
    cvv
    @6
    eqid
    elrnmpt
    ax-mp
    @57
    @19
    @17
    @20
    @57
    @19
    @17
    @56
    @19
    wn
    #
    vy
    cxr
    @31
    @58
    @56
    cpnf
    @5
    wcel
    #
    wn
    @31
    @59
    cpnf
    @1
    clt
    wbr
    #
    @1
    pnfnlt
    @31
    @59
    @41
    cmnf
    cpnf
    cle
    wbr
    #
    @60
    w3a
    #
    @60
    @39
    @31
    @59
    @62
    wb
    mnfxr
    cmnf
    @1
    cpnf
    elico1
    mpan
    @41
    @61
    @60
    simp3
    syl6bi
    mtod
    @56
    @19
    @59
    @18
    @5
    cpnf
    eleq2
    notbid
    syl5ibrcom
    rexlimiv
    pm2.21d
    adantrd
    sylbi
    jaoi
    sylbi
    @23
    @19
    @17
    @20
    @23
    @19
    @17
    @23
    @19
    cpnf
    cr
    wcel
    cpnf
    cr
    pnfnre
    neli
    @23
    @18
    cr
    cpnf
    @23
    @18
    @9
    cuni
    cr
    @18
    @9
    elssuni
    unirnioo
    syl6sseqr
    sseld
    mtoi
    pm2.21d
    adantrd
    jaoi
    sylbi
    rexlimiv
    syl
    sylanb
end
