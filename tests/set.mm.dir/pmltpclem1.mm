include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "wa.mm"
include "wo.mm"
include "cv.mm"
include "w3a.mm"
include "wrex.mm"
include "wceq.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "breq2d.mm"
include "orbi12d.mm"
include "3anbi13d.mm"
include "breq2.mm"
include "anbi12d.mm"
include "3anbi123d.mm"
include "anbi2d.mm"
include "3anbi23d.mm"
include "rspc3ev.mm"
include "syl33anc.mm"

theorem pmltpclem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume pmltpclem1.1: |- ( ph -> A e. S )
  assume pmltpclem1.2: |- ( ph -> B e. S )
  assume pmltpclem1.3: |- ( ph -> C e. S )
  assume pmltpclem1.4: |- ( ph -> A < B )
  assume pmltpclem1.5: |- ( ph -> B < C )
  assume pmltpclem1.6: |- ( ph -> ( ( ( F ` A ) < ( F ` B ) /\ ( F ` C ) < ( F ` B ) ) \/ ( ( F ` B ) < ( F ` A ) /\ ( F ` B ) < ( F ` C ) ) ) )

  disjoint a b
  disjoint a c
  disjoint A a
  disjoint b c
  disjoint A b
  disjoint A c
  disjoint B b
  disjoint B c
  disjoint C c
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint S a
  disjoint S b
  disjoint S c
  assert |- ( ph -> E. a e. S E. b e. S E. c e. S ( a < b /\ b < c /\ ( ( ( F ` a ) < ( F ` b ) /\ ( F ` c ) < ( F ` b ) ) \/ ( ( F ` b ) < ( F ` a ) /\ ( F ` b ) < ( F ` c ) ) ) ) )

  proof
    wph
    cA
    cS
    wcel
    cB
    cS
    wcel
    cC
    cS
    wcel
    cA
    cB
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    clt
    wbr
    #
    cC
    cF
    cfv
    #
    @3
    clt
    wbr
    #
    wa
    #
    @3
    @2
    clt
    wbr
    #
    @3
    @5
    clt
    wbr
    #
    wa
    #
    wo
    #
    va
    cv
    #
    vb
    cv
    #
    clt
    wbr
    #
    @13
    vc
    cv
    #
    clt
    wbr
    #
    @12
    cF
    cfv
    #
    @13
    cF
    cfv
    #
    clt
    wbr
    #
    @15
    cF
    cfv
    #
    @18
    clt
    wbr
    #
    wa
    #
    @18
    @17
    clt
    wbr
    #
    @18
    @20
    clt
    wbr
    #
    wa
    #
    wo
    #
    w3a
    #
    vc
    cS
    wrex
    vb
    cS
    wrex
    va
    cS
    wrex
    pmltpclem1.1
    pmltpclem1.2
    pmltpclem1.3
    pmltpclem1.4
    pmltpclem1.5
    pmltpclem1.6
    @27
    @0
    @1
    @11
    w3a
    cA
    @13
    clt
    wbr
    #
    @16
    @2
    @18
    clt
    wbr
    #
    @21
    wa
    #
    @18
    @2
    clt
    wbr
    #
    @24
    wa
    #
    wo
    #
    w3a
    @0
    cB
    @15
    clt
    wbr
    #
    @4
    @20
    @3
    clt
    wbr
    #
    wa
    #
    @8
    @3
    @20
    clt
    wbr
    #
    wa
    #
    wo
    #
    w3a
    va
    vb
    vc
    cA
    cB
    cC
    cS
    cS
    cS
    @12
    cA
    wceq
    #
    @14
    @28
    @26
    @33
    @16
    @12
    cA
    @13
    clt
    breq1
    @40
    @22
    @30
    @25
    @32
    @40
    @19
    @29
    @21
    @40
    @17
    @2
    @18
    clt
    @12
    cA
    cF
    fveq2
    #
    breq1d
    anbi1d
    @40
    @23
    @31
    @24
    @40
    @17
    @2
    @18
    clt
    @41
    breq2d
    anbi1d
    orbi12d
    3anbi13d
    @13
    cB
    wceq
    #
    @28
    @0
    @16
    @34
    @33
    @39
    @13
    cB
    cA
    clt
    breq2
    @13
    cB
    @15
    clt
    breq1
    @42
    @30
    @36
    @32
    @38
    @42
    @29
    @4
    @21
    @35
    @42
    @18
    @3
    @2
    clt
    @13
    cB
    cF
    fveq2
    #
    breq2d
    @42
    @18
    @3
    @20
    clt
    @43
    breq2d
    anbi12d
    @42
    @31
    @8
    @24
    @37
    @42
    @18
    @3
    @2
    clt
    @43
    breq1d
    @42
    @18
    @3
    @20
    clt
    @43
    breq1d
    anbi12d
    orbi12d
    3anbi123d
    @15
    cC
    wceq
    #
    @34
    @1
    @39
    @11
    @0
    @15
    cC
    cB
    clt
    breq2
    @44
    @36
    @7
    @38
    @10
    @44
    @35
    @6
    @4
    @44
    @20
    @5
    @3
    clt
    @15
    cC
    cF
    fveq2
    #
    breq1d
    anbi2d
    @44
    @37
    @9
    @8
    @44
    @20
    @5
    @3
    clt
    @45
    breq2d
    anbi2d
    orbi12d
    3anbi23d
    rspc3ev
    syl33anc
end
