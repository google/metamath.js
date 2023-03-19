include "cn0.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "crelexp.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cvv.mm"
include "resiexg.mm"
include "relexp0g.mm"
include "syl.mm"
include "dmresi.mm"
include "rnresi.mm"
include "uneq12i.mm"
include "unidm.mm"
include "eqtri.mm"
include "reseq2i.mm"
include "syl6eq.mm"
include "w3a.mm"
include "ccom.mm"
include "wa.mm"
include "wrel.mm"
include "relres.mm"
include "a1i.mm"
include "adantl.mm"
include "relexpsucrd.mm"
include "3impia.mm"
include "simp1.mm"
include "coeq1d.mm"
include "coires1.mm"
include "residm.mm"
include "eqtrd.mm"
include "3exp.mm"
include "com13.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem relexpiidm
  let cA: class A
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ N e. NN0 ) -> ( ( _I |` A ) ^r N ) = ( _I |` A ) )

  proof
    cN
    cn0
    wcel
    cA
    cV
    wcel
    #
    cid
    cA
    cres
    #
    cN
    crelexp
    co
    #
    @1
    wceq
    #
    @0
    @1
    vx
    cv
    #
    crelexp
    co
    #
    @1
    wceq
    #
    wi
    @0
    @1
    cc0
    crelexp
    co
    #
    @1
    wceq
    #
    wi
    @0
    @1
    vy
    cv
    #
    crelexp
    co
    #
    @1
    wceq
    #
    wi
    @0
    @1
    @9
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @1
    wceq
    #
    wi
    @0
    @3
    wi
    vx
    vy
    cN
    @4
    cc0
    wceq
    #
    @6
    @8
    @0
    @15
    @5
    @7
    @1
    @4
    cc0
    @1
    crelexp
    oveq2
    eqeq1d
    imbi2d
    vx
    vy
    weq
    #
    @6
    @11
    @0
    @16
    @5
    @10
    @1
    @4
    @9
    @1
    crelexp
    oveq2
    eqeq1d
    imbi2d
    @4
    @12
    wceq
    #
    @6
    @14
    @0
    @17
    @5
    @13
    @1
    @4
    @12
    @1
    crelexp
    oveq2
    eqeq1d
    imbi2d
    @4
    cN
    wceq
    #
    @6
    @3
    @0
    @18
    @5
    @2
    @1
    @4
    cN
    @1
    crelexp
    oveq2
    eqeq1d
    imbi2d
    @0
    @7
    cid
    @1
    cdm
    #
    @1
    crn
    #
    cun
    #
    cres
    #
    @1
    @0
    @1
    cvv
    wcel
    #
    @7
    @22
    wceq
    cA
    cV
    resiexg
    #
    @1
    cvv
    relexp0g
    syl
    @21
    cA
    cid
    @21
    cA
    cA
    cun
    cA
    @19
    cA
    @20
    cA
    cA
    dmresi
    cA
    rnresi
    uneq12i
    cA
    unidm
    eqtri
    reseq2i
    syl6eq
    @9
    cn0
    wcel
    #
    @0
    @11
    @14
    @11
    @0
    @25
    @14
    @11
    @0
    @25
    @14
    @11
    @0
    @25
    w3a
    #
    @13
    @10
    @1
    ccom
    #
    @1
    @11
    @0
    @25
    @13
    @27
    wceq
    @11
    @0
    wa
    #
    @1
    @9
    @1
    wrel
    @28
    cid
    cA
    relres
    a1i
    @0
    @23
    @11
    @24
    adantl
    relexpsucrd
    3impia
    @26
    @27
    @1
    @1
    ccom
    #
    @1
    @26
    @10
    @1
    @1
    @11
    @0
    @25
    simp1
    coeq1d
    @29
    @1
    cA
    cres
    @1
    @1
    cA
    coires1
    cid
    cA
    residm
    eqtri
    syl6eq
    eqtrd
    3exp
    com13
    a2d
    nn0ind
    impcom
end
