include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cz.mm"
include "clt.mm"
include "csup.mm"
include "cdiv.mm"
include "co.mm"
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
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprzcl.mm"
include "sseldi.mm"

theorem rpnnen1lem2
  let vx: setvar x
  let cT: class T
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  assume rpnnen1lem.1: |- T = { n e. ZZ | ( n / k ) < x }
  assume rpnnen1lem.2: |- F = ( x e. RR |-> ( k e. NN |-> ( sup ( T , RR , < ) / k ) ) )

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
  assert |- ( ( x e. RR /\ k e. NN ) -> sup ( T , RR , < ) e. ZZ )

  proof
    vx
    cv
    #
    cr
    wcel
    #
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    cT
    cz
    cT
    cr
    clt
    csup
    #
    cT
    vn
    cv
    #
    @2
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
    @7
    vn
    cz
    ssrab2
    eqsstri
    #
    @4
    cT
    cz
    wss
    #
    cT
    c0
    wne
    #
    @6
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
    @5
    cT
    wcel
    @10
    @4
    @9
    a1i
    @4
    @8
    c0
    wne
    #
    @11
    @4
    @7
    vn
    cz
    wrex
    #
    @16
    @4
    @17
    @6
    @2
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
    @4
    @18
    cr
    wcel
    #
    @20
    @3
    @1
    @2
    cr
    wcel
    #
    @21
    @2
    nnre
    #
    @22
    @1
    @21
    @2
    @0
    remulcl
    #
    ancoms
    sylan2
    #
    @21
    @20
    @18
    @6
    clt
    wbr
    vn
    cz
    wrex
    vn
    vn
    @18
    btwnz
    simpld
    syl
    @4
    @7
    @19
    vn
    cz
    @4
    @6
    cz
    wcel
    #
    wa
    #
    @6
    cr
    wcel
    #
    @1
    @22
    cc0
    @2
    clt
    wbr
    #
    wa
    #
    @7
    @19
    wb
    @26
    @28
    @4
    @6
    zre
    adantl
    #
    @1
    @3
    @26
    simpll
    #
    @3
    @30
    @1
    @26
    @3
    @22
    @29
    @23
    @2
    nngt0
    jca
    ad2antlr
    @6
    @0
    @2
    ltdivmul
    syl3anc
    #
    rexbidva
    mpbird
    @7
    vn
    cz
    rabn0
    sylibr
    cT
    @8
    c0
    rpnnen1lem.1
    neeq1i
    sylibr
    @4
    @21
    @6
    @18
    cle
    wbr
    #
    vn
    cT
    wral
    #
    @15
    @25
    @4
    @34
    vn
    cT
    @6
    cT
    wcel
    @4
    @26
    @7
    wa
    @34
    @7
    vn
    cT
    cz
    rpnnen1lem.1
    rabeq2i
    @4
    @26
    @7
    @34
    @27
    @7
    @19
    @34
    @33
    @27
    @28
    @21
    @19
    @34
    wi
    @31
    @27
    @22
    @1
    @21
    @3
    @22
    @1
    @26
    @23
    ad2antlr
    @32
    @24
    syl2anc
    @6
    @18
    ltle
    syl2anc
    sylbid
    impr
    sylan2b
    ralrimiva
    @14
    @35
    vy
    @18
    cr
    @12
    @18
    wceq
    @13
    @34
    vn
    cT
    @12
    @18
    @6
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
end
