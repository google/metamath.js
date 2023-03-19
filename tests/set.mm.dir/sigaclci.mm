include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "cv.mm"
include "cdif.mm"
include "ciun.mm"
include "wral.mm"
include "wi.mm"
include "wss.mm"
include "w3a.mm"
include "isrnsigau.mm"
include "simprd.mm"
include "simp2d.mm"
include "adantr.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "elpwi.mm"
include "ssrexv.mm"
include "syl.mm"
include "ss2abdv.mm"
include "wb.mm"
include "uniiunlem.mm"
include "mpbid.mm"
include "sylan9ssr.mm"
include "cvv.mm"
include "abrexexg.mm"
include "elpwg.mm"
include "adantl.mm"
include "mpbird.mm"
include "simp3d.mm"
include "jca.mm"
include "abrexdom2jm.mm"
include "domtr.mm"
include "sylan.mm"
include "ex.mm"
include "breq1.mm"
include "unieq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "sylsyld.mm"
include "ssralv.mm"
include "sylc.mm"
include "dfiun2g.mm"
include "eleq1.mm"
include "3syl.mm"
include "sylibrd.mm"
include "difeq2.mm"
include "rspccv.mm"
include "adantrd.mm"
include "imp.mm"
include "simpr.mm"
include "pwuni.mm"
include "syl6ss.mm"
include "iundifdifd.mm"
include "adantld.mm"
include "syl6.mm"

theorem sigaclci
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( S e. U. ran sigAlgebra /\ A e. ~P S ) /\ ( A ~<_ _om /\ A =/= (/) ) ) -> |^| A e. S )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    #
    cA
    cS
    cpw
    #
    wcel
    #
    wa
    #
    cA
    com
    cdom
    wbr
    #
    cA
    c0
    wne
    #
    wa
    #
    wa
    cA
    cint
    #
    cS
    wcel
    #
    cS
    cuni
    #
    vz
    cA
    @9
    vz
    cv
    #
    cdif
    #
    ciun
    #
    cdif
    #
    cS
    wcel
    #
    @3
    @6
    @14
    @3
    @4
    @14
    @5
    @3
    @9
    vx
    cv
    #
    cdif
    #
    cS
    wcel
    #
    vx
    cS
    wral
    #
    @4
    @12
    cS
    wcel
    #
    @14
    @0
    @18
    @2
    @0
    @9
    cS
    wcel
    #
    @18
    @15
    com
    cdom
    wbr
    #
    @15
    cuni
    #
    cS
    wcel
    #
    wi
    #
    vx
    @1
    wral
    #
    @0
    cS
    @9
    cpw
    #
    wss
    #
    @20
    @18
    @25
    w3a
    vx
    cS
    isrnsigau
    simprd
    #
    simp2d
    adantr
    @3
    @4
    vy
    cv
    @11
    wceq
    #
    vz
    cA
    wrex
    #
    vy
    cab
    #
    cuni
    #
    cS
    wcel
    #
    @19
    @3
    @31
    @1
    wcel
    #
    @25
    wa
    @4
    @31
    com
    cdom
    wbr
    #
    @33
    @3
    @34
    @25
    @3
    @34
    @31
    cS
    wss
    #
    @2
    @0
    @31
    @29
    vz
    cS
    wrex
    #
    vy
    cab
    #
    cS
    @2
    @30
    @37
    vy
    @2
    cA
    cS
    wss
    #
    @30
    @37
    wi
    cA
    cS
    elpwi
    #
    @29
    vz
    cA
    cS
    ssrexv
    syl
    ss2abdv
    @0
    @11
    cS
    wcel
    #
    vz
    cS
    wral
    #
    @38
    cS
    wss
    #
    @0
    @20
    @42
    @10
    com
    cdom
    wbr
    @10
    cuni
    cS
    wcel
    wi
    vz
    @1
    wral
    #
    @0
    @27
    @20
    @42
    @44
    w3a
    vz
    cS
    isrnsigau
    simprd
    simp2d
    #
    @0
    @42
    @42
    @43
    wb
    @45
    vz
    vy
    cS
    @11
    cS
    cS
    uniiunlem
    syl
    mpbid
    sylan9ssr
    @2
    @34
    @36
    wb
    #
    @0
    @2
    @31
    cvv
    wcel
    @46
    vz
    vy
    cA
    @11
    @1
    abrexexg
    @31
    cS
    cvv
    elpwg
    syl
    adantl
    mpbird
    @0
    @25
    @2
    @0
    @20
    @18
    @25
    @28
    simp3d
    adantr
    jca
    @2
    @4
    @35
    wi
    @0
    @2
    @4
    @35
    @2
    @31
    cA
    cdom
    wbr
    @4
    @35
    vy
    vz
    cA
    @11
    @1
    abrexdom2jm
    @31
    cA
    com
    domtr
    sylan
    ex
    adantl
    @24
    @35
    @33
    wi
    vx
    @31
    @1
    @15
    @31
    wceq
    #
    @21
    @35
    @23
    @33
    @15
    @31
    com
    cdom
    breq1
    @47
    @22
    @32
    cS
    @15
    @31
    unieq
    eleq1d
    imbi12d
    rspcva
    sylsyld
    @3
    @41
    vz
    cA
    wral
    #
    @12
    @32
    wceq
    @19
    @33
    wb
    @3
    @39
    @42
    @48
    @2
    @39
    @0
    @40
    adantl
    @0
    @42
    @2
    @45
    adantr
    @41
    vz
    cA
    cS
    ssralv
    sylc
    vz
    vy
    cA
    @11
    cS
    dfiun2g
    @12
    @32
    cS
    eleq1
    3syl
    sylibrd
    @17
    @14
    vx
    @12
    cS
    @15
    @12
    wceq
    @16
    @13
    cS
    @15
    @12
    @9
    difeq2
    eleq1d
    rspccv
    sylsyld
    adantrd
    imp
    @3
    @6
    @8
    @14
    wb
    #
    @3
    @6
    @7
    @13
    wceq
    #
    @49
    @3
    @5
    @50
    @4
    @3
    @2
    cA
    @26
    wss
    @5
    @50
    wi
    @0
    @2
    simpr
    @2
    cA
    cS
    @26
    @40
    cS
    pwuni
    syl6ss
    vz
    cA
    @9
    iundifdifd
    3syl
    adantld
    @7
    @13
    cS
    eleq1
    syl6
    imp
    mpbird
end
