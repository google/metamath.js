include "coe.mm"
include "co.mm"
include "ccnf.mm"
include "ccom.mm"
include "ccnv.mm"
include "wf1o.mm"
include "cdm.mm"
include "eqid.mm"
include "cantnff1o.mm"
include "cv.mm"
include "c0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "crab.mm"
include "cfv.mm"
include "cmpt.mm"
include "f1ocnv.mm"
include "syl.mm"
include "con0.mm"
include "cvv.mm"
include "ssv.mm"
include "sseldi.mm"
include "c1o.mm"
include "eldifad.mm"
include "cdif.mm"
include "wcel.mm"
include "ondif1.mm"
include "simprbi.mm"
include "mapfien.mm"
include "wceq.mm"
include "wb.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "cantnfdm.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "eqtr4d.mm"
include "f1oeq3.mm"
include "mpbird.mm"
include "f1oeq2.mm"
include "f1oco.mm"
include "syl2anc.mm"

theorem oef1o
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  assume oef1o.f: |- ( ph -> F : A -1-1-onto-> C )
  assume oef1o.g: |- ( ph -> G : B -1-1-onto-> D )
  assume oef1o.a: |- ( ph -> A e. ( On \ 1o ) )
  assume oef1o.b: |- ( ph -> B e. On )
  assume oef1o.c: |- ( ph -> C e. On )
  assume oef1o.d: |- ( ph -> D e. On )
  assume oef1o.z: |- ( ph -> ( F ` (/) ) = (/) )
  assume oef1o.k: |- K = ( y e. { x e. ( A ^m B ) | x finSupp (/) } |-> ( F o. ( y o. `' G ) ) )
  assume oef1o.h: |- H = ( ( ( C CNF D ) o. K ) o. `' ( A CNF B ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  assert |- ( ph -> H : ( A ^o B ) -1-1-onto-> ( C ^o D ) )

  proof
    wph
    cA
    cB
    coe
    co
    #
    cC
    cD
    coe
    co
    #
    cC
    cD
    ccnf
    co
    #
    cK
    ccom
    #
    cA
    cB
    ccnf
    co
    #
    ccnv
    #
    ccom
    #
    wf1o
    #
    @0
    @1
    cH
    wf1o
    #
    wph
    @4
    cdm
    #
    @1
    @3
    wf1o
    #
    @0
    @9
    @5
    wf1o
    #
    @7
    wph
    @2
    cdm
    #
    @1
    @2
    wf1o
    @9
    @12
    cK
    wf1o
    #
    @10
    wph
    cC
    cD
    @12
    @12
    eqid
    oef1o.c
    oef1o.d
    cantnff1o
    wph
    @13
    vx
    cv
    #
    c0
    cfsupp
    wbr
    #
    vx
    cA
    cB
    cmap
    co
    crab
    #
    @12
    cK
    wf1o
    #
    wph
    @17
    @16
    @14
    c0
    cF
    cfv
    #
    cfsupp
    wbr
    #
    vx
    cC
    cD
    cmap
    co
    #
    crab
    #
    cK
    wf1o
    #
    wph
    @16
    @21
    vy
    @16
    cF
    vy
    cv
    cG
    ccnv
    #
    ccom
    ccom
    cmpt
    #
    wf1o
    #
    @22
    wph
    vx
    cB
    cA
    cD
    cC
    @16
    @21
    vy
    @23
    cF
    @18
    c0
    @16
    eqid
    #
    @21
    eqid
    @18
    eqid
    wph
    cB
    cD
    cG
    wf1o
    cD
    cB
    @23
    wf1o
    oef1o.g
    cB
    cD
    cG
    f1ocnv
    syl
    oef1o.f
    wph
    con0
    cvv
    cB
    con0
    ssv
    #
    oef1o.b
    sseldi
    wph
    con0
    cvv
    cA
    @27
    wph
    cA
    con0
    c1o
    oef1o.a
    eldifad
    #
    sseldi
    wph
    con0
    cvv
    cD
    @27
    oef1o.d
    sseldi
    wph
    con0
    cvv
    cC
    @27
    oef1o.c
    sseldi
    wph
    cA
    con0
    c1o
    cdif
    wcel
    #
    c0
    cA
    wcel
    #
    oef1o.a
    @29
    cA
    con0
    wcel
    @30
    cA
    ondif1
    simprbi
    syl
    mapfien
    cK
    @24
    wceq
    @22
    @25
    wb
    oef1o.k
    @16
    @21
    cK
    @24
    f1oeq1
    ax-mp
    sylibr
    wph
    @12
    @21
    wceq
    @17
    @22
    wb
    wph
    @12
    @15
    vx
    @20
    crab
    #
    @21
    wph
    cC
    cD
    @31
    vx
    @31
    eqid
    oef1o.c
    oef1o.d
    cantnfdm
    wph
    @19
    @15
    vx
    @20
    wph
    @18
    c0
    @14
    cfsupp
    oef1o.z
    breq2d
    rabbidv
    eqtr4d
    @12
    @21
    @16
    cK
    f1oeq3
    syl
    mpbird
    wph
    @9
    @16
    wceq
    @13
    @17
    wb
    wph
    cA
    cB
    @16
    vx
    @26
    @28
    oef1o.b
    cantnfdm
    @9
    @16
    @12
    cK
    f1oeq2
    syl
    mpbird
    @9
    @12
    @1
    @2
    cK
    f1oco
    syl2anc
    wph
    @9
    @0
    @4
    wf1o
    @11
    wph
    cA
    cB
    @9
    @9
    eqid
    @28
    oef1o.b
    cantnff1o
    @9
    @0
    @4
    f1ocnv
    syl
    @0
    @9
    @1
    @3
    @5
    f1oco
    syl2anc
    cH
    @6
    wceq
    @8
    @7
    wb
    oef1o.h
    @0
    @1
    cH
    @6
    f1oeq1
    ax-mp
    sylibr
end
