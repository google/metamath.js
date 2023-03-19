include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "dmatel.mm"
include "neeq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "neeq2.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "com23.mm"
include "3impia.mm"
include "com12.mm"
include "2a1i.mm"
include "impd.mm"
include "sylbid.mm"
include "imp.mm"

theorem dmatelnd
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  assume dmatid.a: |- A = ( N Mat R )
  assume dmatid.b: |- B = ( Base ` A )
  assume dmatid.0: |- .0. = ( 0g ` R )
  assume dmatid.d: |- D = ( N DMat R )


  assert |- ( ( ( N e. Fin /\ R e. Ring /\ X e. D ) /\ ( I e. N /\ J e. N /\ I =/= J ) ) -> ( I X J ) = .0. )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cX
    cD
    wcel
    #
    w3a
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    cI
    cJ
    wne
    #
    w3a
    #
    cI
    cJ
    cX
    co
    #
    c.0
    wceq
    #
    @0
    @1
    @2
    @6
    @8
    wi
    #
    @0
    @1
    wa
    #
    @2
    cX
    cB
    wcel
    #
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @12
    @13
    cX
    co
    #
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wa
    @9
    cA
    cB
    cD
    cR
    vi
    vj
    cX
    cN
    crg
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatel
    @10
    @11
    @18
    @9
    @18
    @9
    wi
    @10
    @11
    @6
    @18
    @8
    @3
    @4
    @5
    @18
    @8
    wi
    @3
    @4
    wa
    @18
    @5
    @8
    @17
    @5
    @8
    wi
    cI
    @13
    wne
    #
    cI
    @13
    cX
    co
    #
    c.0
    wceq
    #
    wi
    vi
    vj
    cI
    cJ
    cN
    cN
    @12
    cI
    wceq
    #
    @14
    @19
    @16
    @21
    @12
    cI
    @13
    neeq1
    @22
    @15
    @20
    c.0
    @12
    cI
    @13
    cX
    oveq1
    eqeq1d
    imbi12d
    @13
    cJ
    wceq
    #
    @19
    @5
    @21
    @8
    @13
    cJ
    cI
    neeq2
    @23
    @20
    @7
    c.0
    @13
    cJ
    cI
    cX
    oveq2
    eqeq1d
    imbi12d
    rspc2v
    com23
    3impia
    com12
    2a1i
    impd
    sylbid
    3impia
    imp
end
