include "cv.mm"
include "cioo.mm"
include "cq.mm"
include "cxp.mm"
include "cima.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "tgqioo2.mm"
include "simprr.mm"
include "csalg.mm"
include "smfresal.mm"
include "adantr.mm"
include "cvv.mm"
include "iooex.mm"
include "imaexi.mm"
include "a1i.mm"
include "id.mm"
include "ssexd.mm"
include "adantl.mm"
include "simpr.mm"
include "cfv.mm"
include "wrex.mm"
include "wfun.mm"
include "ioofun.mm"
include "fvelima.mm"
include "syl2anc.mm"
include "wi.mm"
include "w3a.mm"
include "c1st.mm"
include "c2nd.mm"
include "co.mm"
include "eqcomd.mm"
include "cop.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "eqcomi.mm"
include "eqtrd.mm"
include "3adant1.mm"
include "cr.mm"
include "cpw.mm"
include "ccnv.mm"
include "crest.mm"
include "ioossre.mm"
include "ovex.mm"
include "elpw.mm"
include "mpbir.mm"
include "csmblfn.mm"
include "cxr.mm"
include "xp1st.mm"
include "qred.mm"
include "rexrd.mm"
include "xp2nd.mm"
include "smfpimioo.mm"
include "jca.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "sylibr.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ssd.mm"
include "sstrd.mm"
include "elpwd.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ssdomg.mm"
include "ax-mp.mm"
include "qct.mm"
include "pm3.2i.mm"
include "xpct.mm"
include "fimact.mm"
include "mp2an.mm"
include "domtr.mm"
include "salunicl.mm"
include "adantrr.mm"
include "ex.mm"
include "exlimdv.mm"

theorem smfpimbor1lem1
  let wph: wff ph
  let cD: class D
  let cS: class S
  let cT: class T
  let ve: setvar e
  let cF: class F
  let cG: class G
  let cJ: class J
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume smfpimbor1lem1.s: |- ( ph -> S e. SAlg )
  assume smfpimbor1lem1.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfpimbor1lem1.a: |- D = dom F
  assume smfpimbor1lem1.j: |- J = ( topGen ` ran (,) )
  assume smfpimbor1lem1.8: |- ( ph -> G e. J )
  assume smfpimbor1lem1.t: |- T = { e e. ~P RR | ( `' F " e ) e. ( S |`t D ) }

  disjoint D e
  disjoint F e
  disjoint S e
  disjoint e ph
  disjoint G q
  disjoint T p
  disjoint T q
  disjoint p q
  disjoint e p
  disjoint p ph
  disjoint ph q
  disjoint k x
  assert |- ( ph -> G e. T )

  proof
    wph
    vq
    cv
    #
    cioo
    cq
    cq
    cxp
    #
    cima
    #
    wss
    #
    cG
    @0
    cuni
    #
    wceq
    #
    wa
    #
    vq
    wex
    cG
    cT
    wcel
    #
    wph
    cG
    cJ
    vq
    smfpimbor1lem1.j
    smfpimbor1lem1.8
    tgqioo2
    wph
    @6
    @7
    vq
    wph
    @6
    @7
    wph
    @6
    wa
    cG
    @4
    cT
    wph
    @3
    @5
    simprr
    wph
    @3
    @4
    cT
    wcel
    @5
    wph
    @3
    wa
    #
    cT
    @0
    wph
    cT
    csalg
    wcel
    @3
    wph
    cD
    cS
    cT
    ve
    cF
    smfpimbor1lem1.s
    smfpimbor1lem1.f
    smfpimbor1lem1.a
    smfpimbor1lem1.t
    smfresal
    adantr
    @8
    @0
    cT
    cvv
    @3
    @0
    cvv
    wcel
    wph
    @3
    @0
    @2
    cvv
    @2
    cvv
    wcel
    #
    @3
    cioo
    @1
    cvv
    iooex
    imaexi
    #
    a1i
    @3
    id
    ssexd
    adantl
    @8
    @0
    @2
    cT
    wph
    @3
    simpr
    wph
    @2
    cT
    wss
    @3
    wph
    vq
    @2
    cT
    wph
    @0
    @2
    wcel
    #
    wa
    vp
    cv
    #
    cioo
    cfv
    #
    @0
    wceq
    #
    vp
    @1
    wrex
    #
    @0
    cT
    wcel
    #
    @11
    @15
    wph
    @11
    cioo
    wfun
    #
    @11
    @15
    @17
    @11
    ioofun
    a1i
    @11
    id
    vp
    @0
    @1
    cioo
    fvelima
    syl2anc
    adantl
    wph
    @15
    @16
    wi
    @11
    wph
    @14
    @16
    vp
    @1
    wph
    @12
    @1
    wcel
    #
    @14
    @16
    wph
    @18
    @14
    w3a
    @0
    @12
    c1st
    cfv
    #
    @12
    c2nd
    cfv
    #
    cioo
    co
    #
    cT
    @18
    @14
    @0
    @21
    wceq
    wph
    @18
    @14
    wa
    @0
    @13
    @21
    @14
    @0
    @13
    wceq
    @18
    @14
    @13
    @0
    @14
    id
    eqcomd
    adantl
    @18
    @13
    @21
    wceq
    @14
    @18
    @13
    @19
    @20
    cop
    #
    cioo
    cfv
    #
    @21
    @18
    @12
    @22
    cioo
    @12
    cq
    cq
    1st2nd2
    fveq2d
    @23
    @21
    wceq
    @18
    @21
    @23
    @19
    @20
    cioo
    df-ov
    eqcomi
    a1i
    eqtrd
    adantr
    eqtrd
    3adant1
    wph
    @18
    @21
    cT
    wcel
    #
    @14
    wph
    @18
    wa
    #
    @21
    cr
    cpw
    #
    wcel
    #
    cF
    ccnv
    #
    @21
    cima
    #
    cS
    cD
    crest
    co
    #
    wcel
    #
    wa
    @24
    @25
    @27
    @31
    @27
    @25
    @27
    @21
    cr
    wss
    @19
    @20
    ioossre
    @21
    cr
    @19
    @20
    cioo
    ovex
    elpw
    mpbir
    a1i
    @25
    @19
    @20
    cD
    cS
    cF
    wph
    cS
    csalg
    wcel
    @18
    smfpimbor1lem1.s
    adantr
    wph
    cF
    cS
    csmblfn
    cfv
    wcel
    @18
    smfpimbor1lem1.f
    adantr
    smfpimbor1lem1.a
    @18
    @19
    cxr
    wcel
    wph
    @18
    @19
    @18
    @19
    @12
    cq
    cq
    xp1st
    qred
    rexrd
    adantl
    @18
    @20
    cxr
    wcel
    wph
    @18
    @20
    @18
    @20
    @12
    cq
    cq
    xp2nd
    qred
    rexrd
    adantl
    smfpimioo
    jca
    @28
    ve
    cv
    #
    cima
    #
    @30
    wcel
    @31
    ve
    @21
    @26
    cT
    @32
    @21
    wceq
    @33
    @29
    @30
    @32
    @21
    @28
    imaeq2
    eleq1d
    smfpimbor1lem1.t
    elrab2
    sylibr
    3adant3
    eqeltrd
    3exp
    rexlimdv
    adantr
    mpd
    ssd
    adantr
    sstrd
    elpwd
    @3
    @0
    com
    cdom
    wbr
    #
    wph
    @3
    @0
    @2
    cdom
    wbr
    #
    @2
    com
    cdom
    wbr
    #
    @34
    @9
    @3
    @35
    wi
    @10
    @0
    @2
    cvv
    ssdomg
    ax-mp
    @36
    @3
    @1
    com
    cdom
    wbr
    #
    @17
    @36
    cq
    com
    cdom
    wbr
    #
    @38
    wa
    @37
    @38
    @38
    qct
    qct
    pm3.2i
    cq
    cq
    xpct
    ax-mp
    ioofun
    @1
    cioo
    fimact
    mp2an
    a1i
    @0
    @2
    com
    domtr
    syl2anc
    adantl
    salunicl
    adantrr
    eqeltrd
    ex
    exlimdv
    mpd
end
