include "clt.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "wa.mm"
include "nfv.mm"
include "cr.mm"
include "adantr.mm"
include "simpr.mm"
include "cioo.mm"
include "climc.mm"
include "cncfiooicclem1.mm"
include "wn.mm"
include "wceq.mm"
include "csn.mm"
include "wss.mm"
include "limccl.mm"
include "sseldi.mm"
include "snssd.mm"
include "ssid.mm"
include "a1i.mm"
include "cncfss.mm"
include "syl2anc.mm"
include "cmpt.mm"
include "cv.mm"
include "cfv.mm"
include "cif.mm"
include "cxr.mm"
include "rexrd.mm"
include "iccid.mm"
include "syl.mm"
include "oveq2.mm"
include "sylan9req.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "elsni.mm"
include "iftrued.mm"
include "mpteq12dva.mm"
include "syl5eq.mm"
include "recnd.mm"
include "cncfdmsn.mm"
include "eqeltrd.mm"
include "sseldd.mm"
include "oveq1d.mm"
include "adantlr.mm"
include "simpll.mm"
include "wo.mm"
include "eqcom.mm"
include "biimpi.mm"
include "con3i.mm"
include "adantl.mm"
include "simplr.mm"
include "pm4.56.mm"
include "lttrid.mm"
include "mpbird.mm"
include "c0.mm"
include "ccn.mm"
include "0ss.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "crest.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "rest0.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "mp2an.mm"
include "eqsstr3i.mm"
include "wb.mm"
include "icc0.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "3eqtrd.mm"
include "0cnf.mm"
include "syl6eqel.mm"
include "pm2.61dan.mm"

theorem cncfiooicc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cL: class L
  let vk: setvar k
  assume cncfiooicc.x: |- F/ x ph
  assume cncfiooicc.g: |- G = ( x e. ( A [,] B ) |-> if ( x = A , R , if ( x = B , L , ( F ` x ) ) ) )
  assume cncfiooicc.a: |- ( ph -> A e. RR )
  assume cncfiooicc.b: |- ( ph -> B e. RR )
  assume cncfiooicc.f: |- ( ph -> F e. ( ( A (,) B ) -cn-> CC ) )
  assume cncfiooicc.l: |- ( ph -> L e. ( F limCC B ) )
  assume cncfiooicc.r: |- ( ph -> R e. ( F limCC A ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint L x
  disjoint R x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> G e. ( ( A [,] B ) -cn-> CC ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    #
    cG
    cA
    cB
    cicc
    co
    #
    cc
    ccncf
    co
    #
    wcel
    #
    wph
    @0
    wa
    #
    vx
    cA
    cB
    cR
    cF
    cG
    cL
    @4
    vx
    nfv
    cncfiooicc.g
    wph
    cA
    cr
    wcel
    #
    @0
    cncfiooicc.a
    adantr
    wph
    cB
    cr
    wcel
    #
    @0
    cncfiooicc.b
    adantr
    wph
    @0
    simpr
    wph
    cF
    cA
    cB
    cioo
    co
    cc
    ccncf
    co
    wcel
    @0
    cncfiooicc.f
    adantr
    wph
    cL
    cF
    cB
    climc
    co
    wcel
    @0
    cncfiooicc.l
    adantr
    wph
    cR
    cF
    cA
    climc
    co
    #
    wcel
    @0
    cncfiooicc.r
    adantr
    cncfiooicclem1
    wph
    @0
    wn
    #
    wa
    #
    cA
    cB
    wceq
    #
    @3
    wph
    @10
    @3
    @8
    wph
    @10
    wa
    #
    cG
    cA
    csn
    #
    cc
    ccncf
    co
    #
    @2
    @11
    @12
    cR
    csn
    #
    ccncf
    co
    #
    @13
    cG
    wph
    @15
    @13
    wss
    #
    @10
    wph
    @14
    cc
    wss
    cc
    cc
    wss
    #
    @16
    wph
    cR
    cc
    wph
    @7
    cc
    cR
    cA
    cF
    limccl
    cncfiooicc.r
    sseldi
    #
    snssd
    @17
    wph
    cc
    ssid
    #
    a1i
    @12
    @14
    cc
    cncfss
    syl2anc
    adantr
    @11
    cG
    vx
    @12
    cR
    cmpt
    #
    @15
    @11
    cG
    vx
    @1
    vx
    cv
    #
    cA
    wceq
    #
    cR
    @21
    cB
    wceq
    cL
    @21
    cF
    cfv
    cif
    #
    cif
    #
    cmpt
    #
    @20
    cncfiooicc.g
    @11
    vx
    @1
    @24
    @12
    cR
    @11
    @12
    @1
    wph
    @10
    @12
    cA
    cA
    cicc
    co
    #
    @1
    wph
    cA
    cxr
    wcel
    #
    @26
    @12
    wceq
    wph
    cA
    cncfiooicc.a
    rexrd
    #
    cA
    iccid
    syl
    cA
    cB
    cA
    cicc
    oveq2
    sylan9req
    #
    eqcomd
    #
    @11
    @21
    @1
    wcel
    #
    wa
    #
    @22
    cR
    @23
    @32
    @21
    @12
    wcel
    @22
    @32
    @21
    @1
    @12
    @11
    @31
    simpr
    @11
    @1
    @12
    wceq
    @31
    @30
    adantr
    eleqtrd
    @21
    cA
    elsni
    syl
    iftrued
    mpteq12dva
    syl5eq
    @11
    cA
    cc
    wcel
    #
    cR
    cc
    wcel
    #
    @20
    @15
    wcel
    wph
    @33
    @10
    wph
    cA
    cncfiooicc.a
    recnd
    adantr
    wph
    @34
    @10
    @18
    adantr
    vx
    cA
    cR
    cncfdmsn
    syl2anc
    eqeltrd
    sseldd
    @11
    @12
    @1
    cc
    ccncf
    @29
    oveq1d
    eleqtrd
    adantlr
    @9
    @10
    wn
    #
    wa
    #
    wph
    cB
    cA
    clt
    wbr
    #
    @3
    wph
    @8
    @35
    simpll
    #
    @36
    @37
    cB
    cA
    wceq
    #
    @0
    wo
    wn
    #
    @36
    @39
    wn
    #
    @8
    @40
    @35
    @41
    @9
    @39
    @10
    @39
    @10
    cB
    cA
    eqcom
    biimpi
    con3i
    adantl
    wph
    @8
    @35
    simplr
    @41
    @8
    wa
    @40
    @39
    @0
    pm4.56
    biimpi
    syl2anc
    @36
    cB
    cA
    @36
    wph
    @6
    @38
    cncfiooicc.b
    syl
    @36
    wph
    @5
    @38
    cncfiooicc.a
    syl
    lttrid
    mpbird
    wph
    @37
    wa
    #
    cG
    c0
    cc
    ccncf
    co
    #
    @2
    @42
    c0
    csn
    #
    @44
    ccn
    co
    #
    @43
    cG
    @45
    c0
    c0
    ccncf
    co
    #
    @43
    c0
    cc
    wss
    #
    @47
    @46
    @45
    wceq
    cc
    0ss
    #
    @48
    c0
    c0
    ccnfld
    ctopn
    cfv
    #
    @44
    @44
    @49
    eqid
    #
    @49
    c0
    crest
    co
    #
    @44
    @49
    ctop
    wcel
    @51
    @44
    wceq
    @49
    @50
    cnfldtop
    @49
    rest0
    ax-mp
    eqcomi
    #
    @52
    cncfcn
    mp2an
    @47
    @17
    @46
    @43
    wss
    @48
    @19
    c0
    c0
    cc
    cncfss
    mp2an
    eqsstr3i
    @42
    cG
    c0
    @45
    @42
    cG
    @25
    vx
    c0
    @24
    cmpt
    #
    c0
    cG
    @25
    wceq
    @42
    cncfiooicc.g
    a1i
    @42
    vx
    @1
    c0
    @24
    @42
    @1
    c0
    wceq
    #
    @37
    wph
    @37
    simpr
    @42
    @27
    cB
    cxr
    wcel
    #
    @54
    @37
    wb
    wph
    @27
    @37
    @28
    adantr
    wph
    @55
    @37
    wph
    cB
    cncfiooicc.b
    rexrd
    adantr
    cA
    cB
    icc0
    syl2anc
    mpbird
    #
    mpteq1d
    @53
    c0
    wceq
    @42
    vx
    @24
    mpt0
    a1i
    3eqtrd
    0cnf
    syl6eqel
    sseldi
    @42
    c0
    @1
    cc
    ccncf
    @42
    @1
    c0
    @56
    eqcomd
    oveq1d
    eleqtrd
    syl2anc
    pm2.61dan
    pm2.61dan
end
