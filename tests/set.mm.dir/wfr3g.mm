include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cpred.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "r19.26.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "wcel.mm"
include "ra4v.mm"
include "predeq3.mm"
include "reseq2d.mm"
include "fveq2d.mm"
include "anbi12d.mm"
include "rspcva.mm"
include "eqtr3.mm"
include "ancoms.mm"
include "ex.mm"
include "syl.mm"
include "expimpd.mm"
include "wss.mm"
include "wb.mm"
include "predss.mm"
include "fvreseq.mm"
include "mpan2.mm"
include "biimpar.mm"
include "eqcomd.mm"
include "syl11.mm"
include "expd.mm"
include "com23.mm"
include "impd.mm"
include "a2d.mm"
include "syl5.mm"
include "wfis2g.mm"
include "r19.21v.mm"
include "sylib.mm"
include "com12.mm"
include "sylan2br.mm"
include "an4s.mm"
include "3impib.mm"
include "eqid.mm"
include "jctil.mm"
include "eqfnfv2.mm"
include "ad2ant2r.mm"
include "3adant1.mm"
include "mpbird.mm"

theorem wfr3g
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let vw: setvar w
  let vz: setvar z

  disjoint A y
  disjoint F y
  disjoint G y
  disjoint H y
  disjoint R y
  disjoint A w
  disjoint A z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint F w
  disjoint F z
  disjoint G w
  disjoint G z
  disjoint H w
  disjoint H z
  disjoint R w
  disjoint R z
  assert |- ( ( ( R We A /\ R Se A ) /\ ( F Fn A /\ A. y e. A ( F ` y ) = ( H ` ( F |` Pred ( R , A , y ) ) ) ) /\ ( G Fn A /\ A. y e. A ( G ` y ) = ( H ` ( G |` Pred ( R , A , y ) ) ) ) ) -> F = G )

  proof
    cA
    cR
    wwe
    cA
    cR
    wse
    wa
    #
    cF
    cA
    wfn
    #
    vy
    cv
    #
    cF
    cfv
    #
    cF
    cA
    cR
    @2
    cpred
    #
    cres
    #
    cH
    cfv
    #
    wceq
    #
    vy
    cA
    wral
    #
    wa
    #
    cG
    cA
    wfn
    #
    @2
    cG
    cfv
    #
    cG
    @4
    cres
    #
    cH
    cfv
    #
    wceq
    #
    vy
    cA
    wral
    #
    wa
    #
    w3a
    #
    cF
    cG
    wceq
    #
    cA
    cA
    wceq
    #
    vz
    cv
    #
    cF
    cfv
    #
    @20
    cG
    cfv
    #
    wceq
    #
    vz
    cA
    wral
    #
    wa
    #
    @17
    @24
    @19
    @0
    @9
    @16
    @24
    @9
    @16
    wa
    @0
    @24
    @1
    @10
    @8
    @15
    @0
    @24
    wi
    #
    @8
    @15
    wa
    @1
    @10
    wa
    #
    @7
    @14
    wa
    #
    vy
    cA
    wral
    #
    @26
    @7
    @14
    vy
    cA
    r19.26
    @0
    @27
    @29
    wa
    #
    @24
    @0
    @30
    @23
    wi
    #
    vz
    cA
    wral
    @30
    @24
    wi
    @31
    @30
    vw
    cv
    #
    cF
    cfv
    #
    @32
    cG
    cfv
    #
    wceq
    #
    wi
    #
    vz
    vw
    cA
    cR
    @20
    @32
    wceq
    #
    @23
    @35
    @30
    @37
    @21
    @33
    @22
    @34
    @20
    @32
    cF
    fveq2
    @20
    @32
    cG
    fveq2
    eqeq12d
    imbi2d
    @36
    vw
    cA
    cR
    @20
    cpred
    #
    wral
    @30
    @35
    vw
    @38
    wral
    #
    wi
    @20
    cA
    wcel
    #
    @31
    @30
    @35
    vw
    @38
    ra4v
    @40
    @30
    @39
    @23
    @40
    @27
    @29
    @39
    @23
    wi
    #
    @40
    @29
    @27
    @41
    @40
    @29
    @27
    @41
    wi
    #
    @40
    @29
    wa
    @21
    cF
    @38
    cres
    #
    cH
    cfv
    #
    wceq
    #
    @22
    cG
    @38
    cres
    #
    cH
    cfv
    #
    wceq
    #
    wa
    #
    @42
    @28
    @49
    vy
    @20
    cA
    @2
    @20
    wceq
    #
    @7
    @45
    @14
    @48
    @50
    @3
    @21
    @6
    @44
    @2
    @20
    cF
    fveq2
    @50
    @5
    @43
    cH
    @50
    @4
    @38
    cF
    cA
    cR
    @2
    @20
    predeq3
    #
    reseq2d
    fveq2d
    eqeq12d
    @50
    @11
    @22
    @13
    @47
    @2
    @20
    cG
    fveq2
    @50
    @12
    @46
    cH
    @50
    @4
    @38
    cG
    @51
    reseq2d
    fveq2d
    eqeq12d
    anbi12d
    rspcva
    @49
    @27
    @39
    @23
    @47
    @44
    wceq
    #
    @49
    @23
    @27
    @39
    wa
    #
    @52
    @45
    @48
    @23
    @52
    @45
    wa
    @21
    @47
    wceq
    #
    @48
    @23
    wi
    @45
    @52
    @54
    @21
    @47
    @44
    eqtr3
    ancoms
    @54
    @48
    @23
    @21
    @22
    @47
    eqtr3
    ex
    syl
    expimpd
    @53
    @46
    @43
    cH
    @53
    @43
    @46
    @27
    @43
    @46
    wceq
    #
    @39
    @27
    @38
    cA
    wss
    @55
    @39
    wb
    cA
    cR
    @20
    predss
    vw
    cA
    @38
    cF
    cG
    fvreseq
    mpan2
    biimpar
    eqcomd
    fveq2d
    syl11
    expd
    syl
    ex
    com23
    impd
    a2d
    syl5
    wfis2g
    @30
    @23
    vz
    cA
    r19.21v
    sylib
    com12
    sylan2br
    an4s
    com12
    3impib
    cA
    eqid
    jctil
    @9
    @16
    @18
    @25
    wb
    #
    @0
    @1
    @10
    @56
    @8
    @15
    vz
    cA
    cA
    cF
    cG
    eqfnfv2
    ad2ant2r
    3adant1
    mpbird
end
