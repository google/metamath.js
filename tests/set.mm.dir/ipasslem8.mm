include "cc0.mm"
include "cc.mm"
include "wcel.mm"
include "cq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccl.mm"
include "cr.mm"
include "wceq.mm"
include "wf.mm"
include "0cn.mm"
include "cv.mm"
include "wral.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "qre.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "wa.mm"
include "qcn.mm"
include "cnv.mm"
include "phnvi.mm"
include "nvscl.mm"
include "mp3an1.mm"
include "sylan.mm"
include "dipcl.mm"
include "mp3an13.mm"
include "ipasslem5.mm"
include "subeq0bd.mm"
include "mpan2.mm"
include "eqtrd.mm"
include "rgen.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "funmpt2.mm"
include "qssre.mm"
include "dmmpti.mm"
include "sseqtr4i.mm"
include "funconstss.mm"
include "mp2an.mm"
include "mpbi.mm"
include "qdensere.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ct1.mm"
include "ccn.mm"
include "w3a.mm"
include "cha.mm"
include "eqid.mm"
include "cnfldhaus.mm"
include "haust1.mm"
include "ax-mp.mm"
include "ipasslem7.mm"
include "uniretop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "dnsconst.mm"
include "mpanl12.mm"
include "mp3an.mm"

theorem ipasslem8
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let cK: class K
  let vy: setvar y
  let cN: class N
  assume ip1i.1: |- X = ( BaseSet ` U )
  assume ip1i.2: |- G = ( +v ` U )
  assume ip1i.4: |- S = ( .sOLD ` U )
  assume ip1i.7: |- P = ( .iOLD ` U )
  assume ip1i.9: |- U e. CPreHilOLD
  assume ipasslem7.a: |- A e. X
  assume ipasslem7.b: |- B e. X
  assume ipasslem7.f: |- F = ( w e. RR |-> ( ( ( w S A ) P B ) - ( w x. ( A P B ) ) ) )

  disjoint B w
  disjoint P w
  disjoint S w
  disjoint U w
  disjoint X w
  disjoint A w
  disjoint F x
  disjoint K w
  disjoint w x
  disjoint A x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  assert |- F : RR --> { 0 }

  proof
    cc0
    cc
    wcel
    #
    cq
    cF
    ccnv
    cc0
    csn
    #
    cima
    wss
    #
    cq
    cioo
    crn
    ctg
    cfv
    #
    ccl
    cfv
    cfv
    cr
    wceq
    #
    cr
    @1
    cF
    wf
    #
    0cn
    vx
    cv
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    vx
    cq
    wral
    #
    @2
    @8
    vx
    cq
    @6
    cq
    wcel
    #
    @7
    @6
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @6
    cA
    cB
    cP
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cc0
    @10
    @6
    cr
    wcel
    @7
    @15
    wceq
    @6
    qre
    vw
    @6
    vw
    cv
    #
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @16
    @13
    cmul
    co
    #
    cmin
    co
    #
    @15
    cr
    cF
    @16
    @6
    wceq
    #
    @18
    @12
    @19
    @14
    cmin
    @21
    @17
    @11
    cB
    cP
    @16
    @6
    cA
    cS
    oveq1
    oveq1d
    @16
    @6
    @13
    cmul
    oveq1
    oveq12d
    ipasslem7.f
    @12
    @14
    cmin
    ovex
    fvmpt
    syl
    @10
    cA
    cX
    wcel
    #
    @15
    cc0
    wceq
    ipasslem7.a
    @10
    @22
    wa
    #
    @12
    @14
    @23
    @11
    cX
    wcel
    #
    @12
    cc
    wcel
    #
    @10
    @6
    cc
    wcel
    #
    @22
    @24
    @6
    qcn
    cU
    cnv
    wcel
    #
    @26
    @22
    @24
    cU
    ip1i.9
    phnvi
    #
    @6
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvscl
    mp3an1
    sylan
    @27
    @24
    cB
    cX
    wcel
    @25
    @28
    ipasslem7.b
    @11
    cB
    cP
    cU
    cX
    ip1i.1
    ip1i.7
    dipcl
    mp3an13
    syl
    cA
    cB
    @6
    cP
    cS
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipasslem7.b
    ipasslem5
    subeq0bd
    mpan2
    eqtrd
    rgen
    cF
    wfun
    cq
    cF
    cdm
    #
    wss
    @9
    @2
    wb
    vw
    cr
    @20
    cF
    ipasslem7.f
    funmpt2
    cq
    cr
    @29
    qssre
    vw
    cr
    @20
    cF
    @18
    @19
    cmin
    ovex
    ipasslem7.f
    dmmpti
    sseqtr4i
    vx
    cq
    cc0
    cF
    funconstss
    mp2an
    mpbi
    qdensere
    ccnfld
    ctopn
    cfv
    #
    ct1
    wcel
    #
    cF
    @3
    @30
    ccn
    co
    wcel
    @0
    @2
    @4
    w3a
    @5
    @30
    cha
    wcel
    @31
    @30
    @30
    eqid
    #
    cnfldhaus
    @30
    haust1
    ax-mp
    vw
    cA
    cB
    cP
    cS
    cU
    cF
    cG
    @3
    @30
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipasslem7.a
    ipasslem7.b
    ipasslem7.f
    @3
    eqid
    @32
    ipasslem7
    cq
    cc0
    cF
    @3
    @30
    cr
    cc
    uniretop
    cc
    @30
    @30
    @32
    cnfldtopon
    toponunii
    dnsconst
    mpanl12
    mp3an
end
