include "csslt.mm"
include "wbr.mm"
include "cv.mm"
include "csn.mm"
include "cbday.mm"
include "cfv.mm"
include "cun.mm"
include "cima.mm"
include "cuni.mm"
include "csuc.mm"
include "wss.mm"
include "w3a.mm"
include "csur.mm"
include "wrex.mm"
include "cslt.mm"
include "wral.mm"
include "cvv.mm"
include "wcel.mm"
include "ssltss1.mm"
include "ssltex1.mm"
include "ssltss2.mm"
include "ssltex2.mm"
include "ssltsep.mm"
include "noeta.mm"
include "syl221anc.mm"
include "wa.mm"
include "brsslt.mm"
include "df-3an.mm"
include "bianass.mm"
include "bitri.mm"
include "adantr.mm"
include "snex.mm"
include "jctir.mm"
include "snssi.mm"
include "adantl.mm"
include "jca32.mm"
include "biantrurd.mm"
include "bicomd.mm"
include "vex.mm"
include "breq2.mm"
include "ralsn.mm"
include "ralbii.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "jctil.mm"
include "weq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "3anbi12d.mm"
include "rexbidva.mm"
include "mpbird.mm"

theorem etasslt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  assert |- ( A <<s B -> E. x e. No ( A <<s { x } /\ { x } <<s B /\ ( bday ` x ) C_ suc U. ( bday " ( A u. B ) ) ) )

  proof
    cA
    cB
    csslt
    wbr
    #
    cA
    vx
    cv
    #
    csn
    #
    csslt
    wbr
    #
    @2
    cB
    csslt
    wbr
    #
    @1
    cbday
    cfv
    cbday
    cA
    cB
    cun
    cima
    cuni
    csuc
    wss
    #
    w3a
    #
    vx
    csur
    wrex
    vy
    cv
    #
    @1
    cslt
    wbr
    #
    vy
    cA
    wral
    #
    @1
    vz
    cv
    #
    cslt
    wbr
    #
    vz
    cB
    wral
    #
    @5
    w3a
    #
    vx
    csur
    wrex
    #
    @0
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    cB
    csur
    wss
    #
    cB
    cvv
    wcel
    #
    @7
    @10
    cslt
    wbr
    #
    vz
    cB
    wral
    #
    vy
    cA
    wral
    @14
    cA
    cB
    ssltss1
    #
    cA
    cB
    ssltex1
    #
    cA
    cB
    ssltss2
    #
    cA
    cB
    ssltex2
    #
    vy
    vz
    cA
    cB
    ssltsep
    vy
    vz
    vx
    cA
    cB
    cvv
    cvv
    noeta
    syl221anc
    @0
    @6
    @13
    vx
    csur
    @0
    @1
    csur
    wcel
    #
    wa
    #
    @3
    @9
    @4
    @12
    @5
    @3
    @16
    @2
    cvv
    wcel
    #
    wa
    #
    @15
    @2
    csur
    wss
    #
    wa
    #
    wa
    #
    @19
    vz
    @2
    wral
    #
    vy
    cA
    wral
    #
    wa
    #
    @26
    @9
    @3
    @28
    @15
    @29
    @33
    w3a
    #
    wa
    @34
    vy
    vz
    cA
    @2
    brsslt
    @35
    @30
    @33
    @28
    @15
    @29
    @33
    df-3an
    bianass
    bitri
    @26
    @34
    @33
    @9
    @26
    @33
    @34
    @26
    @31
    @33
    @26
    @28
    @15
    @29
    @26
    @16
    @27
    @0
    @16
    @25
    @22
    adantr
    @1
    snex
    #
    jctir
    @0
    @15
    @25
    @21
    adantr
    @25
    @29
    @0
    @1
    csur
    snssi
    adantl
    #
    jca32
    biantrurd
    bicomd
    @32
    @8
    vy
    cA
    @19
    @8
    vz
    @1
    vx
    vex
    #
    @10
    @1
    @7
    cslt
    breq2
    ralsn
    ralbii
    syl6bb
    syl5bb
    @26
    @4
    @20
    vy
    @2
    wral
    #
    @12
    @4
    @27
    @18
    wa
    #
    @29
    @17
    wa
    #
    wa
    #
    @39
    wa
    #
    @26
    @39
    @4
    @40
    @29
    @17
    @39
    w3a
    #
    wa
    @43
    vy
    vz
    @2
    cB
    brsslt
    @44
    @41
    @39
    @40
    @29
    @17
    @39
    df-3an
    bianass
    bitri
    @26
    @39
    @43
    @26
    @42
    @39
    @26
    @40
    @29
    @17
    @26
    @18
    @27
    @0
    @18
    @25
    @24
    adantr
    @36
    jctil
    @37
    @0
    @17
    @25
    @23
    adantr
    jca32
    biantrurd
    bicomd
    syl5bb
    @20
    @12
    vy
    @1
    @38
    vy
    vx
    weq
    @19
    @11
    vz
    cB
    @7
    @1
    @10
    cslt
    breq1
    ralbidv
    ralsn
    syl6bb
    3anbi12d
    rexbidva
    mpbird
end
