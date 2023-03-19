include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "eqidd.mm"
include "wa.mm"
include "nn0uz.mm"
include "0zd.mm"
include "id.mm"
include "wf.mm"
include "a1i.mm"
include "algrp1.mm"
include "algrf.mm"
include "ffvelrnda.mm"
include "eqeq12d.mm"
include "vtoclga.mm"
include "syl.mm"
include "eqtrd.mm"
include "biimprd.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem alginv
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cI: class I
  let cK: class K
  let vk: setvar k
  let vz: setvar z
  assume alginv.1: |- R = seq 0 ( ( F o. 1st ) , ( NN0 X. { A } ) )
  assume alginv.2: |- F : S --> S
  assume alginv.3: |- I Fn S
  assume alginv.4: |- ( x e. S -> ( I ` ( F ` x ) ) = ( I ` x ) )

  disjoint F x
  disjoint I x
  disjoint R x
  disjoint S x
  disjoint k z
  disjoint A k
  disjoint A z
  disjoint k x
  disjoint I k
  disjoint x z
  disjoint I z
  disjoint R k
  disjoint R z
  disjoint S k
  disjoint S z
  disjoint K z
  assert |- ( ( A e. S /\ K e. NN0 ) -> ( I ` ( R ` K ) ) = ( I ` ( R ` 0 ) ) )

  proof
    cK
    cn0
    wcel
    cA
    cS
    wcel
    #
    cK
    cR
    cfv
    #
    cI
    cfv
    #
    cc0
    cR
    cfv
    #
    cI
    cfv
    #
    wceq
    #
    @0
    vz
    cv
    #
    cR
    cfv
    #
    cI
    cfv
    #
    @4
    wceq
    #
    wi
    @0
    @4
    @4
    wceq
    #
    wi
    @0
    vk
    cv
    #
    cR
    cfv
    #
    cI
    cfv
    #
    @4
    wceq
    #
    wi
    @0
    @11
    c1
    caddc
    co
    #
    cR
    cfv
    #
    cI
    cfv
    #
    @4
    wceq
    #
    wi
    @0
    @5
    wi
    vz
    vk
    cK
    @6
    cc0
    wceq
    #
    @9
    @10
    @0
    @19
    @8
    @4
    @4
    @19
    @7
    @3
    cI
    @6
    cc0
    cR
    fveq2
    fveq2d
    eqeq1d
    imbi2d
    @6
    @11
    wceq
    #
    @9
    @14
    @0
    @20
    @8
    @13
    @4
    @20
    @7
    @12
    cI
    @6
    @11
    cR
    fveq2
    fveq2d
    eqeq1d
    imbi2d
    @6
    @15
    wceq
    #
    @9
    @18
    @0
    @21
    @8
    @17
    @4
    @21
    @7
    @16
    cI
    @6
    @15
    cR
    fveq2
    fveq2d
    eqeq1d
    imbi2d
    @6
    cK
    wceq
    #
    @9
    @5
    @0
    @22
    @8
    @2
    @4
    @22
    @7
    @1
    cI
    @6
    cK
    cR
    fveq2
    fveq2d
    eqeq1d
    imbi2d
    @0
    @4
    eqidd
    @11
    cn0
    wcel
    #
    @0
    @14
    @18
    @0
    @23
    @14
    @18
    wi
    @0
    @23
    wa
    #
    @18
    @14
    @24
    @17
    @13
    @4
    @24
    @17
    @12
    cF
    cfv
    #
    cI
    cfv
    #
    @13
    @24
    @16
    @25
    cI
    @0
    cA
    cR
    cS
    cF
    @11
    cc0
    cn0
    nn0uz
    alginv.1
    @0
    0zd
    #
    @0
    id
    #
    cS
    cS
    cF
    wf
    @0
    alginv.2
    a1i
    #
    algrp1
    fveq2d
    @24
    @12
    cS
    wcel
    @26
    @13
    wceq
    #
    @0
    cn0
    cS
    @11
    cR
    @0
    cA
    cR
    cS
    cF
    cc0
    cn0
    nn0uz
    alginv.1
    @27
    @28
    @29
    algrf
    ffvelrnda
    vx
    cv
    #
    cF
    cfv
    #
    cI
    cfv
    #
    @31
    cI
    cfv
    #
    wceq
    @30
    vx
    @12
    cS
    @31
    @12
    wceq
    #
    @33
    @26
    @34
    @13
    @35
    @32
    @25
    cI
    @31
    @12
    cF
    fveq2
    fveq2d
    @31
    @12
    cI
    fveq2
    eqeq12d
    alginv.4
    vtoclga
    syl
    eqtrd
    eqeq1d
    biimprd
    expcom
    a2d
    nn0ind
    impcom
end
