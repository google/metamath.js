include "cbrsiga.mm"
include "csx.mm"
include "co.mm"
include "ctx.mm"
include "csigagen.mm"
include "cfv.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt2.mm"
include "crn.mm"
include "cr.mm"
include "csiga.mm"
include "wcel.mm"
include "wceq.mm"
include "brsigarn.mm"
include "eqid.mm"
include "sxval.mm"
include "mp2an.mm"
include "cuni.mm"
include "wss.mm"
include "ctopon.mm"
include "br2base.mm"
include "tpr2uni.mm"
include "eqtr4i.mm"
include "wral.mm"
include "wa.mm"
include "c1st.mm"
include "cres.mm"
include "ccnv.mm"
include "cima.mm"
include "c2nd.mm"
include "cin.mm"
include "cpw.mm"
include "brsigasspwrn.mm"
include "sseli.mm"
include "elpwid.mm"
include "xpinpreima2.mm"
include "syl2an.mm"
include "tpr2tp.mm"
include "sigagensiga.mm"
include "ax-mp.mm"
include "elrnsiga.mm"
include "mp1i.mm"
include "a1i.mm"
include "sgsiga.mm"
include "ccn.mm"
include "cioo.mm"
include "ctg.mm"
include "retopon.mm"
include "eqeltri.mm"
include "tx1cn.mm"
include "eqidd.mm"
include "df-brsiga.mm"
include "fveq2i.mm"
include "cnmbfm.mm"
include "id.mm"
include "mbfmcnvima.mm"
include "adantr.mm"
include "tx2cn.mm"
include "adantl.mm"
include "inelsiga.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "rgen2a.mm"
include "rnmpt2ss.mm"
include "sigagenss2.mm"
include "mp3an.mm"
include "eqsstri.mm"
include "sxbrsigalem6.mm"
include "eqssi.mm"

theorem sxbrsiga
  let cJ: class J
  let ve: setvar e
  let vf: setvar f
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )


  assert |- ( BrSiga sX BrSiga ) = ( sigaGen ` ( J tX J ) )

  proof
    cbrsiga
    cbrsiga
    csx
    co
    #
    cJ
    cJ
    ctx
    co
    #
    csigagen
    cfv
    #
    @0
    ve
    vf
    cbrsiga
    cbrsiga
    ve
    cv
    #
    vf
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    csigagen
    cfv
    #
    @2
    cbrsiga
    cr
    csiga
    cfv
    #
    wcel
    #
    @10
    @0
    @8
    wceq
    brsigarn
    brsigarn
    ve
    vf
    @7
    cbrsiga
    cbrsiga
    @9
    @9
    @7
    eqid
    sxval
    mp2an
    @7
    cuni
    #
    @1
    cuni
    #
    wceq
    @7
    @2
    wss
    #
    @1
    cr
    cr
    cxp
    #
    ctopon
    cfv
    #
    wcel
    #
    @8
    @2
    wss
    @11
    @14
    @12
    ve
    vf
    br2base
    cJ
    sxbrsiga.0
    tpr2uni
    eqtr4i
    @5
    @2
    wcel
    #
    vf
    cbrsiga
    wral
    ve
    cbrsiga
    wral
    @13
    @17
    ve
    vf
    cbrsiga
    @3
    cbrsiga
    wcel
    #
    @4
    cbrsiga
    wcel
    #
    wa
    #
    @5
    c1st
    @14
    cres
    #
    ccnv
    @3
    cima
    #
    c2nd
    @14
    cres
    #
    ccnv
    @4
    cima
    #
    cin
    #
    @2
    @18
    @3
    cr
    wss
    @4
    cr
    wss
    @5
    @25
    wceq
    @19
    @18
    @3
    cr
    cbrsiga
    cr
    cpw
    #
    @3
    brsigasspwrn
    sseli
    elpwid
    @19
    @4
    cr
    cbrsiga
    @26
    @4
    brsigasspwrn
    sseli
    elpwid
    @3
    @4
    cr
    cr
    xpinpreima2
    syl2an
    @20
    @2
    csiga
    crn
    cuni
    #
    wcel
    #
    @22
    @2
    wcel
    #
    @24
    @2
    wcel
    #
    @25
    @2
    wcel
    @2
    @12
    csiga
    cfv
    wcel
    #
    @28
    @20
    @16
    @31
    cJ
    sxbrsiga.0
    tpr2tp
    #
    @1
    @15
    sigagensiga
    ax-mp
    @2
    @12
    elrnsiga
    mp1i
    @18
    @29
    @19
    @18
    @3
    @2
    cbrsiga
    @21
    @18
    @1
    @15
    @16
    @18
    @32
    a1i
    sgsiga
    @10
    cbrsiga
    @27
    wcel
    #
    @18
    brsigarn
    cbrsiga
    cr
    elrnsiga
    #
    mp1i
    @18
    @2
    cbrsiga
    @21
    @1
    cJ
    @21
    @1
    cJ
    ccn
    co
    #
    wcel
    #
    @18
    cJ
    cr
    ctopon
    cfv
    #
    wcel
    #
    @38
    @36
    cJ
    cioo
    crn
    ctg
    cfv
    #
    @37
    sxbrsiga.0
    retopon
    eqeltri
    #
    @40
    cJ
    cJ
    cr
    cr
    tx1cn
    mp2an
    a1i
    @18
    @2
    eqidd
    cbrsiga
    cJ
    csigagen
    cfv
    #
    wceq
    #
    @18
    cbrsiga
    @39
    csigagen
    cfv
    @41
    df-brsiga
    cJ
    @39
    csigagen
    sxbrsiga.0
    fveq2i
    eqtr4i
    #
    a1i
    cnmbfm
    @18
    id
    mbfmcnvima
    adantr
    @19
    @30
    @18
    @19
    @4
    @2
    cbrsiga
    @23
    @19
    @1
    @15
    @16
    @19
    @32
    a1i
    sgsiga
    @10
    @33
    @19
    brsigarn
    @34
    mp1i
    @19
    @2
    cbrsiga
    @23
    @1
    cJ
    @23
    @35
    wcel
    #
    @19
    @38
    @38
    @44
    @40
    @40
    cJ
    cJ
    cr
    cr
    tx2cn
    mp2an
    a1i
    @19
    @2
    eqidd
    @42
    @19
    @43
    a1i
    cnmbfm
    @19
    id
    mbfmcnvima
    adantl
    @22
    @24
    @2
    inelsiga
    syl3anc
    eqeltrd
    rgen2a
    ve
    vf
    cbrsiga
    cbrsiga
    @5
    @2
    @6
    @6
    eqid
    rnmpt2ss
    ax-mp
    @32
    @7
    @1
    @15
    sigagenss2
    mp3an
    eqsstri
    cJ
    sxbrsiga.0
    sxbrsigalem6
    eqssi
end
