include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cmap.mm"
include "crab.mm"
include "cdioph.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "ccom.mm"
include "wsbc.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "simplr.mm"
include "ovex.mm"
include "mapco2.mm"
include "syl2anc.mm"
include "biantrurd.mm"
include "nfcv.mm"
include "elrabsf.mm"
include "syl6bbr.mm"
include "rabbidva.mm"
include "3adant3.mm"
include "diophren.mm"
include "3coml.mm"
include "eqeltrd.mm"

theorem rabrenfdioph
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b

  disjoint b ph
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint F a
  disjoint F b
  assert |- ( ( B e. NN0 /\ F : ( 1 ... A ) --> ( 1 ... B ) /\ { a e. ( NN0 ^m ( 1 ... A ) ) | ph } e. ( Dioph ` A ) ) -> { b e. ( NN0 ^m ( 1 ... B ) ) | [. ( b o. F ) / a ]. ph } e. ( Dioph ` B ) )

  proof
    cB
    cn0
    wcel
    #
    c1
    cA
    cfz
    co
    #
    c1
    cB
    cfz
    co
    #
    cF
    wf
    #
    wph
    va
    cn0
    @1
    cmap
    co
    #
    crab
    #
    cA
    cdioph
    cfv
    wcel
    #
    w3a
    wph
    va
    vb
    cv
    #
    cF
    ccom
    #
    wsbc
    #
    vb
    cn0
    @2
    cmap
    co
    #
    crab
    #
    @8
    @5
    wcel
    #
    vb
    @10
    crab
    #
    cB
    cdioph
    cfv
    #
    @0
    @3
    @11
    @13
    wceq
    @6
    @0
    @3
    wa
    #
    @9
    @12
    vb
    @10
    @15
    @7
    @10
    wcel
    #
    wa
    #
    @9
    @8
    @4
    wcel
    #
    @9
    wa
    @12
    @17
    @18
    @9
    @17
    @16
    @3
    @18
    @15
    @16
    simpr
    @0
    @3
    @16
    simplr
    @7
    cn0
    @2
    cF
    @1
    c1
    cA
    cfz
    ovex
    mapco2
    syl2anc
    biantrurd
    wph
    va
    @8
    @4
    va
    @4
    nfcv
    elrabsf
    syl6bbr
    rabbidva
    3adant3
    @6
    @0
    @3
    @13
    @14
    wcel
    @5
    cF
    cB
    cA
    vb
    diophren
    3coml
    eqeltrd
end
