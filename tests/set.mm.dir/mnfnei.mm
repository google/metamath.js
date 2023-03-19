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
include "wn.mm"
include "clt.mm"
include "wbr.mm"
include "nltmnf.mm"
include "w3a.mm"
include "pnfxr.mm"
include "elioc1.mm"
include "mpan2.mm"
include "simp2.mm"
include "syl6bi.mm"
include "mtod.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "pm2.21d.mm"
include "adantrd.mm"
include "sylbi.mm"
include "cc0.mm"
include "cif.mm"
include "mnfxr.mm"
include "a1i.mm"
include "0xr.mm"
include "simprl.mm"
include "ifcl.mm"
include "sylancr.mm"
include "mnflt0.mm"
include "simpll.mm"
include "simprr.mm"
include "eleqtrd.mm"
include "elico1.mm"
include "mpbid.mm"
include "simp3d.mm"
include "breq2.mm"
include "ifboth.mm"
include "xrmin1.mm"
include "0re.mm"
include "ltpnf.mm"
include "mp1i.mm"
include "xrlelttrd.mm"
include "xrre2.mm"
include "syl32anc.mm"
include "xrmin2.mm"
include "df-ico.mm"
include "xrltletr.mm"
include "ixxss2.mm"
include "syl2anc.mm"
include "simplr.mm"
include "eqsstr3d.mm"
include "sstrd.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "rexlimdvaa.mm"
include "com12.mm"
include "jaoi.mm"
include "mnfnre.mm"
include "neli.mm"
include "cuni.mm"
include "elssuni.mm"
include "unirnioo.mm"
include "syl6sseqr.mm"
include "sseld.mm"
include "mtoi.mm"
include "syl.mm"
include "sylanb.mm"

theorem mnfnei
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
  assert |- ( ( A e. ( ordTop ` <_ ) /\ -oo e. A ) -> E. x e. RR ( -oo [,) x ) C_ A )

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
    cmnf
    cA
    wcel
    #
    cmnf
    vx
    cv
    #
    cico
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
    cmnf
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
    cmnf
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
    @28
    @19
    @17
    @20
    @28
    @19
    @17
    @27
    @19
    wn
    #
    vy
    cxr
    @1
    cxr
    wcel
    #
    @31
    @27
    cmnf
    @2
    wcel
    #
    wn
    @32
    @33
    @1
    cmnf
    clt
    wbr
    #
    @1
    nltmnf
    @32
    @33
    cmnf
    cxr
    wcel
    #
    @34
    cmnf
    cpnf
    cle
    wbr
    #
    w3a
    #
    @34
    @32
    cpnf
    cxr
    wcel
    #
    @33
    @37
    wb
    pnfxr
    @1
    cpnf
    cmnf
    elioc1
    mpan2
    @35
    @34
    @36
    simp2
    syl6bi
    mtod
    @27
    @19
    @33
    @18
    @2
    cmnf
    eleq2
    notbid
    syl5ibrcom
    rexlimiv
    pm2.21d
    adantrd
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
    @40
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
    @21
    @40
    @17
    @21
    @39
    @17
    vy
    cxr
    @21
    @32
    @39
    wa
    #
    wa
    #
    cc0
    @1
    cle
    wbr
    #
    cc0
    @1
    cif
    #
    cr
    wcel
    #
    cmnf
    @44
    cico
    co
    #
    cA
    wss
    #
    @17
    @42
    @35
    @44
    cxr
    wcel
    #
    @38
    cmnf
    @44
    clt
    wbr
    #
    @44
    cpnf
    clt
    wbr
    @45
    @35
    @42
    mnfxr
    a1i
    @42
    cc0
    cxr
    wcel
    #
    @32
    @48
    0xr
    @21
    @32
    @39
    simprl
    #
    @43
    cc0
    @1
    cxr
    ifcl
    sylancr
    #
    @38
    @42
    pnfxr
    a1i
    #
    @42
    cmnf
    cc0
    clt
    wbr
    #
    cmnf
    @1
    clt
    wbr
    #
    @49
    mnflt0
    @42
    @35
    cmnf
    cmnf
    cle
    wbr
    #
    @55
    @42
    cmnf
    @5
    wcel
    #
    @35
    @56
    @55
    w3a
    #
    @42
    cmnf
    @18
    @5
    @19
    @20
    @41
    simpll
    @21
    @32
    @39
    simprr
    #
    eleqtrd
    @42
    @35
    @32
    @57
    @58
    wb
    mnfxr
    @51
    cmnf
    @1
    cmnf
    elico1
    sylancr
    mpbid
    simp3d
    @43
    @54
    @55
    @49
    cc0
    @1
    cc0
    @44
    cmnf
    clt
    breq2
    @1
    @44
    cmnf
    clt
    breq2
    ifboth
    sylancr
    @42
    @44
    cc0
    cpnf
    @52
    @50
    @42
    0xr
    a1i
    @53
    @42
    @50
    @32
    @44
    cc0
    cle
    wbr
    0xr
    @51
    cc0
    @1
    xrmin1
    sylancr
    cc0
    cr
    wcel
    cc0
    cpnf
    clt
    wbr
    @42
    0re
    cc0
    ltpnf
    mp1i
    xrlelttrd
    cmnf
    @44
    cpnf
    xrre2
    syl32anc
    @42
    @46
    @5
    cA
    @42
    @32
    @44
    @1
    cle
    wbr
    #
    @46
    @5
    wss
    @51
    @42
    @50
    @32
    @60
    0xr
    @51
    cc0
    @1
    xrmin2
    sylancr
    va
    vb
    vc
    vx
    cmnf
    @44
    @1
    cico
    cle
    clt
    clt
    cico
    cle
    va
    vb
    vc
    df-ico
    #
    @61
    @14
    @44
    @1
    xrltletr
    ixxss2
    syl2anc
    @42
    @5
    @18
    cA
    @59
    @19
    @20
    @41
    simplr
    eqsstr3d
    sstrd
    @16
    @47
    vx
    @44
    cr
    @14
    @44
    wceq
    @15
    @46
    cA
    @14
    @44
    cmnf
    cico
    oveq2
    sseq1d
    rspcev
    syl2anc
    rexlimdvaa
    com12
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
    cmnf
    cr
    wcel
    cmnf
    cr
    mnfnre
    neli
    @23
    @18
    cr
    cmnf
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
