include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wreu.mm"
include "wn.mm"
include "4cycl2v2nb.mm"
include "wrex.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "preq2.mm"
include "preq1.mm"
include "preq12d.mm"
include "sseq1d.mm"
include "anbi1d.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "neeq2.mm"
include "rspc2ev.mm"
include "3expa.mm"
include "expcom.mm"
include "ex.mm"
include "com13.mm"
include "3impia.mm"
include "impcom.mm"
include "rexnal.mm"
include "annim.mm"
include "df-ne.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "bitr3i.mm"
include "rexbii.mm"
include "sylibr.mm"
include "intnand.mm"
include "reu4.mm"
include "sylnibr.mm"
include "stoic3.mm"

theorem 4cycl2vnunb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint E x
  disjoint V x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint D y
  disjoint E y
  disjoint V y
  assert |- ( ( ( { A , B } e. E /\ { B , C } e. E ) /\ ( { C , D } e. E /\ { D , A } e. E ) /\ ( B e. V /\ D e. V /\ B =/= D ) ) -> -. E! x e. V { { A , x } , { x , C } } C_ E )

  proof
    cA
    cB
    cpr
    #
    cE
    wcel
    cB
    cC
    cpr
    #
    cE
    wcel
    wa
    cC
    cD
    cpr
    cE
    wcel
    cD
    cA
    cpr
    cE
    wcel
    wa
    @0
    @1
    cpr
    #
    cE
    wss
    #
    cA
    cD
    cpr
    #
    cD
    cC
    cpr
    #
    cpr
    #
    cE
    wss
    #
    wa
    #
    cB
    cV
    wcel
    #
    cD
    cV
    wcel
    #
    cB
    cD
    wne
    #
    w3a
    #
    cA
    vx
    cv
    #
    cpr
    #
    @13
    cC
    cpr
    #
    cpr
    #
    cE
    wss
    #
    vx
    cV
    wreu
    #
    wn
    cA
    cB
    cC
    cD
    cE
    4cycl2v2nb
    @8
    @12
    wa
    #
    @17
    vx
    cV
    wrex
    #
    @17
    cA
    vy
    cv
    #
    cpr
    #
    @21
    cC
    cpr
    #
    cpr
    #
    cE
    wss
    #
    wa
    #
    @13
    @21
    wceq
    #
    wi
    #
    vy
    cV
    wral
    #
    vx
    cV
    wral
    #
    wa
    @18
    @19
    @30
    @20
    @19
    @26
    @13
    @21
    wne
    #
    wa
    #
    vy
    cV
    wrex
    #
    vx
    cV
    wrex
    #
    @30
    wn
    #
    @12
    @8
    @34
    @9
    @10
    @11
    @8
    @34
    wi
    @8
    @11
    @9
    @10
    wa
    #
    @34
    @8
    @11
    @36
    @34
    wi
    @36
    @8
    @11
    wa
    #
    @34
    @9
    @10
    @37
    @34
    @32
    @37
    @3
    @25
    wa
    #
    cB
    @21
    wne
    #
    wa
    vx
    vy
    cB
    cD
    cV
    cV
    @13
    cB
    wceq
    #
    @26
    @38
    @31
    @39
    @40
    @17
    @3
    @25
    @40
    @16
    @2
    cE
    @40
    @14
    @0
    @15
    @1
    @13
    cB
    cA
    preq2
    @13
    cB
    cC
    preq1
    preq12d
    sseq1d
    anbi1d
    @13
    cB
    @21
    neeq1
    anbi12d
    @21
    cD
    wceq
    #
    @38
    @8
    @39
    @11
    @41
    @25
    @7
    @3
    @41
    @24
    @6
    cE
    @41
    @22
    @4
    @23
    @5
    @21
    cD
    cA
    preq2
    @21
    cD
    cC
    preq1
    preq12d
    sseq1d
    anbi2d
    @21
    cD
    cB
    neeq2
    anbi12d
    rspc2ev
    3expa
    expcom
    ex
    com13
    3impia
    impcom
    @35
    @29
    wn
    #
    vx
    cV
    wrex
    @34
    @29
    vx
    cV
    rexnal
    @42
    @33
    vx
    cV
    @42
    @28
    wn
    #
    vy
    cV
    wrex
    @33
    @28
    vy
    cV
    rexnal
    @43
    @32
    vy
    cV
    @43
    @26
    @27
    wn
    #
    wa
    @32
    @26
    @27
    annim
    @44
    @31
    @26
    @31
    @44
    @13
    @21
    df-ne
    bicomi
    anbi2i
    bitr3i
    rexbii
    bitr3i
    rexbii
    bitr3i
    sylibr
    intnand
    @17
    @25
    vx
    vy
    cV
    @27
    @16
    @24
    cE
    @27
    @14
    @22
    @15
    @23
    @13
    @21
    cA
    preq2
    @13
    @21
    cC
    preq1
    preq12d
    sseq1d
    reu4
    sylnibr
    stoic3
end
