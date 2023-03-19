include "cr.mm"
include "wcel.mm"
include "cioo.mm"
include "crn.mm"
include "w3a.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "c1.mm"
include "c2.mm"
include "clogb.mm"
include "cfl.mm"
include "cfv.mm"
include "eqid.mm"
include "dya2icoseg.mm"
include "ralrimiva.mm"
include "3ad2ant1.mm"
include "cabs.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cbl.mm"
include "simp3.mm"
include "ctg.mm"
include "cvv.mm"
include "iooex.mm"
include "rnex.mm"
include "bastg.mm"
include "ax-mp.mm"
include "simp2.mm"
include "sseldi.mm"
include "syl6eleqr.mm"
include "cxmt.mm"
include "wb.mm"
include "rexmet.mm"
include "crefld.mm"
include "cxme.mm"
include "cmopn.mm"
include "wceq.mm"
include "ccms.mm"
include "cmt.mm"
include "recms.mm"
include "cmsms.mm"
include "msxms.mm"
include "mp2b.mm"
include "ctopn.mm"
include "retopn.mm"
include "eqtri.mm"
include "rebase.mm"
include "cds.mm"
include "reds.mm"
include "reseq1i.mm"
include "xmstopn.mm"
include "elmopn2.mm"
include "simprbi.mm"
include "syl.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "rpre.mm"
include "bl2ioo.mm"
include "sylan2.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "r19.29.mm"
include "r19.41v.mm"
include "sstr.mm"
include "anim2i.mm"
include "anassrs.mm"
include "reximi.mm"
include "sylbir.mm"
include "rexlimivw.mm"

theorem dya2icoseg2
  let vx: setvar x
  let vn: setvar n
  let cE: class E
  let cI: class I
  let cJ: class J
  let cX: class X
  let vb: setvar b
  let vd: setvar d
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )

  disjoint b n
  disjoint b x
  disjoint n x
  disjoint E b
  disjoint E x
  disjoint I b
  disjoint X b
  disjoint X x
  disjoint n x
  disjoint I x
  disjoint b d
  disjoint d x
  disjoint E d
  disjoint I d
  disjoint X d
  assert |- ( ( X e. RR /\ E e. ran (,) /\ X e. E ) -> E. b e. ran I ( X e. b /\ b C_ E ) )

  proof
    cX
    cr
    wcel
    #
    cE
    cioo
    crn
    #
    wcel
    #
    cX
    cE
    wcel
    #
    w3a
    #
    cX
    vb
    cv
    #
    wcel
    #
    @5
    cX
    vd
    cv
    #
    cmin
    co
    cX
    @7
    caddc
    co
    cioo
    co
    #
    wss
    #
    wa
    #
    vb
    cI
    crn
    #
    wrex
    #
    @8
    cE
    wss
    #
    wa
    #
    vd
    crp
    wrex
    #
    @6
    @5
    cE
    wss
    #
    wa
    #
    vb
    @11
    wrex
    #
    @4
    @12
    vd
    crp
    wral
    #
    @13
    vd
    crp
    wrex
    #
    @15
    @0
    @2
    @19
    @3
    @0
    @12
    vd
    crp
    vx
    @7
    vn
    cI
    cJ
    c1
    c2
    @7
    clogb
    co
    cmin
    co
    cfl
    cfv
    #
    cX
    vb
    sxbrsiga.0
    dya2ioc.1
    @21
    eqid
    dya2icoseg
    ralrimiva
    3ad2ant1
    @4
    cX
    @7
    cabs
    cmin
    ccom
    #
    cr
    cr
    cxp
    #
    cres
    #
    cbl
    cfv
    #
    co
    #
    cE
    wss
    #
    vd
    crp
    wrex
    #
    @20
    @4
    @3
    vx
    cv
    #
    @7
    @25
    co
    #
    cE
    wss
    #
    vd
    crp
    wrex
    #
    vx
    cE
    wral
    #
    @28
    @0
    @2
    @3
    simp3
    @4
    cE
    cJ
    wcel
    #
    @33
    @4
    cE
    @1
    ctg
    cfv
    #
    cJ
    @4
    @1
    @35
    cE
    @1
    cvv
    wcel
    @1
    @35
    wss
    cioo
    iooex
    rnex
    @1
    cvv
    bastg
    ax-mp
    @0
    @2
    @3
    simp2
    sseldi
    sxbrsiga.0
    syl6eleqr
    @34
    cE
    cr
    wss
    #
    @33
    @24
    cr
    cxmt
    cfv
    wcel
    @34
    @36
    @33
    wa
    wb
    @24
    @24
    eqid
    #
    rexmet
    vx
    vd
    cE
    @24
    cJ
    cr
    crefld
    cxme
    wcel
    #
    cJ
    @24
    cmopn
    cfv
    wceq
    crefld
    ccms
    wcel
    crefld
    cmt
    wcel
    @38
    recms
    crefld
    cmsms
    crefld
    msxms
    mp2b
    @24
    cJ
    crefld
    cr
    cJ
    @35
    crefld
    ctopn
    cfv
    sxbrsiga.0
    retopn
    eqtri
    rebase
    @22
    crefld
    cds
    cfv
    @23
    reds
    reseq1i
    xmstopn
    ax-mp
    elmopn2
    ax-mp
    simprbi
    syl
    @32
    @28
    vx
    cX
    cE
    @29
    cX
    wceq
    #
    @31
    @27
    vd
    crp
    @39
    @30
    @26
    cE
    @29
    cX
    @7
    @25
    oveq1
    sseq1d
    rexbidv
    rspcva
    syl2anc
    @0
    @2
    @28
    @20
    wb
    @3
    @0
    @27
    @13
    vd
    crp
    @7
    crp
    wcel
    @0
    @7
    cr
    wcel
    #
    @27
    @13
    wb
    @7
    rpre
    @0
    @40
    wa
    @26
    @8
    cE
    cX
    @7
    @24
    @37
    bl2ioo
    sseq1d
    sylan2
    rexbidva
    3ad2ant1
    mpbid
    @12
    @13
    vd
    crp
    r19.29
    syl2anc
    @14
    @18
    vd
    crp
    @14
    @10
    @13
    wa
    #
    vb
    @11
    wrex
    @18
    @10
    @13
    vb
    @11
    r19.41v
    @41
    @17
    vb
    @11
    @6
    @9
    @13
    @17
    @9
    @13
    wa
    @16
    @6
    @5
    @8
    cE
    sstr
    anim2i
    anassrs
    reximi
    sylbir
    rexlimivw
    syl
end
