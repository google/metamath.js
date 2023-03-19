include "wfr.mm"
include "wse.mm"
include "wa.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cpred.mm"
include "cres.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "wcel.mm"
include "wi.mm"
include "ra4v.mm"
include "r19.26.mm"
include "anbi2i.mm"
include "fveq2.mm"
include "id.mm"
include "predeq3.mm"
include "reseq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "rspcva.mm"
include "eqtr3.mm"
include "eqcomd.mm"
include "ex.mm"
include "syl.mm"
include "expimpd.mm"
include "wss.mm"
include "wb.mm"
include "predss.mm"
include "fvreseq.mm"
include "mpan2.mm"
include "biimpar.mm"
include "oveq2d.mm"
include "syl11.mm"
include "expd.mm"
include "com23.mm"
include "impd.mm"
include "syl5bir.mm"
include "a2d.mm"
include "syl5.mm"
include "imbi2d.mm"
include "frins2g.mm"
include "rsp.mm"
include "com3r.mm"
include "an4s.mm"
include "com12.mm"
include "3impib.mm"
include "ralrimiv.mm"
include "eqid.mm"
include "jctil.mm"
include "eqfnfv2.mm"
include "ad2ant2r.mm"
include "3adant1.mm"
include "mpbird.mm"

theorem frr3g
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
  assert |- ( ( ( R Fr A /\ R Se A ) /\ ( F Fn A /\ A. y e. A ( F ` y ) = ( y H ( F |` Pred ( R , A , y ) ) ) ) /\ ( G Fn A /\ A. y e. A ( G ` y ) = ( y H ( G |` Pred ( R , A , y ) ) ) ) ) -> F = G )

  proof
    cA
    cR
    wfr
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
    @2
    cF
    cA
    cR
    @2
    cpred
    #
    cres
    #
    cH
    co
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
    @2
    cG
    @4
    cres
    #
    cH
    co
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
    @17
    @23
    vz
    cA
    @0
    @9
    @16
    @20
    cA
    wcel
    #
    @23
    wi
    #
    @9
    @16
    wa
    @0
    @27
    @1
    @10
    @8
    @15
    @0
    @27
    wi
    @0
    @26
    @1
    @10
    wa
    #
    @8
    @15
    wa
    #
    wa
    #
    @23
    @0
    @30
    @23
    wi
    #
    vz
    cA
    wral
    @26
    @31
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
    @37
    wral
    #
    wi
    @26
    @31
    @30
    @35
    vw
    @37
    ra4v
    @26
    @30
    @38
    @23
    @30
    @28
    @7
    @14
    wa
    #
    vy
    cA
    wral
    #
    wa
    @26
    @38
    @23
    wi
    #
    @40
    @29
    @28
    @7
    @14
    vy
    cA
    r19.26
    anbi2i
    @26
    @28
    @40
    @41
    @26
    @40
    @28
    @41
    @26
    @40
    @28
    @41
    wi
    #
    @26
    @40
    wa
    @21
    @20
    cF
    @37
    cres
    #
    cH
    co
    #
    wceq
    #
    @22
    @20
    cG
    @37
    cres
    #
    cH
    co
    #
    wceq
    #
    wa
    #
    @42
    @39
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
    @2
    @20
    @5
    @43
    cH
    @50
    id
    #
    @50
    @4
    @37
    cF
    cA
    cR
    @2
    @20
    predeq3
    #
    reseq2d
    oveq12d
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
    @2
    @20
    @12
    @46
    cH
    @51
    @50
    @4
    @37
    cG
    @52
    reseq2d
    oveq12d
    eqeq12d
    anbi12d
    rspcva
    @49
    @28
    @38
    @23
    @47
    @44
    wceq
    #
    @49
    @23
    @28
    @38
    wa
    #
    @53
    @45
    @48
    @23
    @53
    @45
    wa
    #
    @21
    @47
    wceq
    #
    @48
    @23
    wi
    @55
    @47
    @21
    @47
    @21
    @44
    eqtr3
    eqcomd
    @56
    @48
    @23
    @21
    @22
    @47
    eqtr3
    ex
    syl
    expimpd
    @54
    @44
    @47
    @54
    @43
    @46
    @20
    cH
    @28
    @43
    @46
    wceq
    #
    @38
    @28
    @37
    cA
    wss
    @57
    @38
    wb
    cA
    cR
    @20
    predss
    vw
    cA
    @37
    cF
    cG
    fvreseq
    mpan2
    biimpar
    oveq2d
    eqcomd
    syl11
    expd
    syl
    ex
    com23
    impd
    syl5bir
    a2d
    syl5
    @20
    @32
    wceq
    #
    @23
    @35
    @30
    @58
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
    frins2g
    @31
    vz
    cA
    rsp
    syl
    com3r
    an4s
    com12
    3impib
    ralrimiv
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
    @59
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
