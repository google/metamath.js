include "wcel.mm"
include "c1.mm"
include "co.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "cs1.mm"
include "csn.mm"
include "wa.mm"
include "cword.mm"
include "oveqi.mm"
include "a1i.mm"
include "clwwlknon.mm"
include "chash.mm"
include "cvtx.mm"
include "cedg.mm"
include "w3a.mm"
include "clwwlkn1.mm"
include "anbi1i.mm"
include "eqcomi.mm"
include "wrdeqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "ad2antrl.mm"
include "adantr.mm"
include "simpl1.mm"
include "simpr.mm"
include "3jca.mm"
include "adantl.mm"
include "wb.mm"
include "wrdl1s1.mm"
include "mpbird.mm"
include "wi.mm"
include "sneq.mm"
include "eleq12d.mm"
include "biimpd.mm"
include "com13.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "impcom.mm"
include "jca32.mm"
include "fveq2.mm"
include "s1len.mm"
include "syl6eq.mm"
include "fveq1.mm"
include "s1fv.mm"
include "sylan9eq.mm"
include "eqcomd.mm"
include "sneqd.mm"
include "impancom.mm"
include "ex.mm"
include "jca.mm"
include "impbida.mm"
include "syl5bb.mm"
include "rabbidva2.mm"
include "3eqtrd.mm"

theorem clwwlknon1
  let vw: setvar w
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  assume clwwlknon1.v: |- V = ( Vtx ` G )
  assume clwwlknon1.c: |- C = ( ClWWalksNOn ` G )
  assume clwwlknon1.e: |- E = ( Edg ` G )

  disjoint G w
  disjoint V w
  disjoint X w
  assert |- ( X e. V -> ( X C 1 ) = { w e. Word V | ( w = <" X "> /\ { X } e. E ) } )

  proof
    cX
    cV
    wcel
    #
    cX
    c1
    cC
    co
    #
    cX
    c1
    cG
    cclwwlknon
    cfv
    #
    co
    #
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    vw
    c1
    cG
    cclwwlkn
    co
    #
    crab
    #
    @4
    cX
    cs1
    #
    wceq
    #
    cX
    csn
    #
    cE
    wcel
    #
    wa
    #
    vw
    cV
    cword
    #
    crab
    @1
    @3
    wceq
    @0
    cC
    @2
    cX
    c1
    clwwlknon1.c
    oveqi
    a1i
    @3
    @8
    wceq
    @0
    vw
    cG
    c1
    cX
    clwwlknon
    a1i
    @0
    @6
    @13
    vw
    @7
    @14
    @4
    @7
    wcel
    #
    @6
    wa
    @4
    chash
    cfv
    #
    c1
    wceq
    #
    @4
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @5
    csn
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    w3a
    #
    @6
    wa
    #
    @0
    @4
    @14
    wcel
    #
    @13
    wa
    #
    @15
    @24
    @6
    cG
    @4
    clwwlkn1
    anbi1i
    @0
    @25
    @27
    @0
    @25
    wa
    #
    @26
    @10
    @12
    @24
    @26
    @0
    @6
    @20
    @17
    @26
    @23
    @20
    @26
    @19
    @14
    @4
    @18
    cV
    cV
    @18
    clwwlknon1.v
    eqcomi
    wrdeqi
    eleq2i
    biimpi
    3ad2ant2
    #
    ad2antrl
    @28
    @10
    @26
    @17
    @6
    w3a
    #
    @25
    @30
    @0
    @25
    @26
    @17
    @6
    @24
    @26
    @6
    @29
    adantr
    @17
    @20
    @23
    @6
    simpl1
    @24
    @6
    simpr
    3jca
    adantl
    @0
    @10
    @30
    wb
    @25
    cX
    cV
    @4
    wrdl1s1
    adantr
    mpbird
    @25
    @0
    @12
    @24
    @6
    @0
    @12
    wi
    #
    @23
    @17
    @6
    @31
    wi
    @20
    @0
    @6
    @23
    @12
    @6
    @23
    @12
    wi
    wi
    @0
    @6
    @23
    @12
    @6
    @21
    @11
    @22
    cE
    @5
    cX
    sneq
    @22
    cE
    wceq
    @6
    cE
    @22
    clwwlknon1.e
    eqcomi
    a1i
    eleq12d
    biimpd
    a1i
    com13
    3ad2ant3
    imp
    impcom
    jca32
    @0
    @27
    wa
    #
    @24
    @6
    @32
    @17
    @20
    @23
    @27
    @17
    @0
    @10
    @17
    @26
    @12
    @10
    @16
    @9
    chash
    cfv
    c1
    @4
    @9
    chash
    fveq2
    cX
    s1len
    syl6eq
    ad2antrl
    adantl
    @26
    @20
    @0
    @13
    @26
    @20
    @14
    @19
    @4
    cV
    @18
    clwwlknon1.v
    wrdeqi
    eleq2i
    biimpi
    ad2antrl
    @27
    @0
    @23
    @13
    @0
    @23
    wi
    @26
    @10
    @0
    @12
    @23
    @10
    @0
    wa
    #
    @12
    @23
    @33
    @11
    @21
    cE
    @22
    @33
    cX
    @5
    @33
    @5
    cX
    @10
    @0
    @5
    cc0
    @9
    cfv
    cX
    cc0
    @4
    @9
    fveq1
    cX
    cV
    s1fv
    sylan9eq
    #
    eqcomd
    sneqd
    cE
    @22
    wceq
    @33
    clwwlknon1.e
    a1i
    eleq12d
    biimpd
    impancom
    adantl
    impcom
    3jca
    @27
    @0
    @6
    @10
    @0
    @6
    wi
    @26
    @12
    @10
    @0
    @6
    @34
    ex
    ad2antrl
    impcom
    jca
    impbida
    syl5bb
    rabbidva2
    3eqtrd
end
