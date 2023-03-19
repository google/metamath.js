include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "cfv.mm"
include "cn.mm"
include "clt.mm"
include "csup.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cq.mm"
include "cmap.mm"
include "cvv.mm"
include "wceq.mm"
include "mptex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "wf.mm"
include "cz.mm"
include "wa.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "a1i.mm"
include "cmul.mm"
include "nnre.mm"
include "remulcl.mm"
include "ancoms.mm"
include "sylan2.mm"
include "btwnz.mm"
include "simpld.mm"
include "syl.mm"
include "cc0.mm"
include "wb.mm"
include "zre.mm"
include "adantl.mm"
include "simpll.mm"
include "nngt0.mm"
include "jca.mm"
include "ad2antlr.mm"
include "ltdivmul.mm"
include "syl3anc.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "rabn0.mm"
include "sylibr.mm"
include "neeq1i.mm"
include "rabeq2i.mm"
include "wi.mm"
include "syl2anc.mm"
include "ltle.mm"
include "sylbid.mm"
include "impr.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprzcl.mm"
include "sseldi.mm"
include "znq.mm"
include "sylancom.mm"
include "eqid.mm"
include "fmptd.mm"
include "elmap.mm"
include "eqeltrd.mm"

theorem rpnnen1lem1
  let vx: setvar x
  let cT: class T
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  assume rpnnen1lem.1: |- T = { n e. ZZ | ( n / k ) < x }
  assume rpnnen1lem.2: |- F = ( x e. RR |-> ( k e. NN |-> ( sup ( T , RR , < ) / k ) ) )
  assume rpnnen1lem.n: |- NN e. _V
  assume rpnnen1lem.q: |- QQ e. _V

  disjoint F k
  disjoint F n
  disjoint F x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint T n
  disjoint F y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint T y
  assert |- ( x e. RR -> ( F ` x ) e. ( QQ ^m NN ) )

  proof
    vx
    cv
    #
    cr
    wcel
    #
    @0
    cF
    cfv
    #
    vk
    cn
    cT
    cr
    clt
    csup
    #
    vk
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    cq
    cn
    cmap
    co
    #
    @1
    @6
    cvv
    wcel
    @2
    @6
    wceq
    vk
    cn
    @5
    rpnnen1lem.n
    mptex
    vx
    cr
    @6
    cvv
    cF
    rpnnen1lem.2
    fvmpt2
    mpan2
    @1
    cn
    cq
    @6
    wf
    @6
    @7
    wcel
    @1
    vk
    cn
    @5
    cq
    @6
    @1
    @4
    cn
    wcel
    #
    @3
    cz
    wcel
    @5
    cq
    wcel
    @1
    @8
    wa
    #
    cT
    cz
    @3
    cT
    vn
    cv
    #
    @4
    cdiv
    co
    @0
    clt
    wbr
    #
    vn
    cz
    crab
    #
    cz
    rpnnen1lem.1
    @11
    vn
    cz
    ssrab2
    eqsstri
    #
    @9
    cT
    cz
    wss
    #
    cT
    c0
    wne
    #
    @10
    vy
    cv
    #
    cle
    wbr
    #
    vn
    cT
    wral
    #
    vy
    cr
    wrex
    #
    @3
    cT
    wcel
    @14
    @9
    @13
    a1i
    @9
    @12
    c0
    wne
    #
    @15
    @9
    @11
    vn
    cz
    wrex
    #
    @20
    @9
    @21
    @10
    @4
    @0
    cmul
    co
    #
    clt
    wbr
    #
    vn
    cz
    wrex
    #
    @9
    @22
    cr
    wcel
    #
    @24
    @8
    @1
    @4
    cr
    wcel
    #
    @25
    @4
    nnre
    #
    @26
    @1
    @25
    @4
    @0
    remulcl
    #
    ancoms
    sylan2
    #
    @25
    @24
    @22
    @10
    clt
    wbr
    vn
    cz
    wrex
    vn
    vn
    @22
    btwnz
    simpld
    syl
    @9
    @11
    @23
    vn
    cz
    @9
    @10
    cz
    wcel
    #
    wa
    #
    @10
    cr
    wcel
    #
    @1
    @26
    cc0
    @4
    clt
    wbr
    #
    wa
    #
    @11
    @23
    wb
    @30
    @32
    @9
    @10
    zre
    adantl
    #
    @1
    @8
    @30
    simpll
    #
    @8
    @34
    @1
    @30
    @8
    @26
    @33
    @27
    @4
    nngt0
    jca
    ad2antlr
    @10
    @0
    @4
    ltdivmul
    syl3anc
    #
    rexbidva
    mpbird
    @11
    vn
    cz
    rabn0
    sylibr
    cT
    @12
    c0
    rpnnen1lem.1
    neeq1i
    sylibr
    @9
    @25
    @10
    @22
    cle
    wbr
    #
    vn
    cT
    wral
    #
    @19
    @29
    @9
    @38
    vn
    cT
    @10
    cT
    wcel
    @9
    @30
    @11
    wa
    @38
    @11
    vn
    cT
    cz
    rpnnen1lem.1
    rabeq2i
    @9
    @30
    @11
    @38
    @31
    @11
    @23
    @38
    @37
    @31
    @32
    @25
    @23
    @38
    wi
    @35
    @31
    @26
    @1
    @25
    @8
    @26
    @1
    @30
    @27
    ad2antlr
    @36
    @28
    syl2anc
    @10
    @22
    ltle
    syl2anc
    sylbid
    impr
    sylan2b
    ralrimiva
    @18
    @39
    vy
    @22
    cr
    @16
    @22
    wceq
    @17
    @38
    vn
    cT
    @16
    @22
    @10
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    vy
    vn
    cT
    suprzcl
    syl3anc
    sseldi
    @3
    @4
    znq
    sylancom
    @6
    eqid
    fmptd
    cq
    cn
    @6
    rpnnen1lem.q
    rpnnen1lem.n
    elmap
    sylibr
    eqeltrd
end
