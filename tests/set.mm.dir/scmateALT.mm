include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cif.mm"
include "wrex.mm"
include "wi.mm"
include "weq.mm"
include "wral.mm"
include "crab.mm"
include "scmatmats.mm"
include "eleq2d.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "rexbidv.mm"
include "elrab.mm"
include "oveq1.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "eqeq2.mm"
include "rspc2v.mm"
include "reximdv.mm"
include "com12.mm"
include "adantl.mm"
include "a1i.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "ex.mm"
include "3imp1.mm"

theorem scmateALT
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vc: setvar c
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  assume scmatmat.a: |- A = ( N Mat R )
  assume scmatmat.b: |- B = ( Base ` A )
  assume scmatmat.s: |- S = ( N ScMat R )
  assume scmate.k: |- K = ( Base ` R )
  assume scmate.0: |- .0. = ( 0g ` R )

  disjoint M c
  disjoint N c
  disjoint R c
  disjoint I c
  disjoint J c
  disjoint K c
  disjoint S c
  disjoint B c
  disjoint M m
  disjoint A i
  disjoint A j
  disjoint i j
  disjoint B i
  disjoint B j
  disjoint B m
  disjoint c i
  disjoint c j
  disjoint c m
  disjoint i m
  disjoint j m
  disjoint K i
  disjoint K j
  disjoint N i
  disjoint N j
  disjoint N m
  disjoint R i
  disjoint R j
  disjoint R m
  disjoint I i
  disjoint I j
  disjoint J j
  disjoint K m
  disjoint M i
  disjoint M j
  disjoint .0. i
  disjoint .0. j
  disjoint .0. m
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ M e. S ) /\ ( I e. N /\ J e. N ) ) -> E. c e. K ( I M J ) = if ( I = J , c , .0. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cS
    wcel
    #
    cI
    cN
    wcel
    cJ
    cN
    wcel
    wa
    #
    cI
    cJ
    cM
    co
    #
    cI
    cJ
    wceq
    #
    vc
    cv
    #
    c.0
    cif
    #
    wceq
    #
    vc
    cK
    wrex
    #
    @0
    @1
    @2
    @3
    @9
    wi
    #
    wi
    @0
    @1
    wa
    #
    @2
    cM
    vi
    cv
    #
    vj
    cv
    #
    vm
    cv
    #
    co
    #
    vi
    vj
    weq
    #
    @6
    c.0
    cif
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    vc
    cK
    wrex
    #
    vm
    cB
    crab
    #
    wcel
    #
    @10
    @11
    cS
    @21
    cM
    cA
    cB
    cR
    cS
    vi
    vj
    vm
    cK
    cN
    c.0
    vc
    scmatmat.a
    scmatmat.b
    scmatmat.s
    scmate.k
    scmate.0
    scmatmats
    eleq2d
    @22
    cM
    cB
    wcel
    #
    @12
    @13
    cM
    co
    #
    @17
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    vc
    cK
    wrex
    #
    wa
    #
    @11
    @10
    @20
    @27
    vm
    cM
    cB
    @14
    cM
    wceq
    #
    @19
    @26
    vc
    cK
    @29
    @18
    @25
    vi
    vj
    cN
    cN
    @29
    @15
    @24
    @17
    @12
    @13
    @14
    cM
    oveq
    eqeq1d
    2ralbidv
    rexbidv
    elrab
    @28
    @10
    wi
    @11
    @27
    @10
    @23
    @3
    @27
    @9
    @3
    @26
    @8
    vc
    cK
    @25
    @8
    cI
    @13
    cM
    co
    #
    cI
    @13
    wceq
    #
    @6
    c.0
    cif
    #
    wceq
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
    @24
    @30
    @17
    @32
    @12
    cI
    @13
    cM
    oveq1
    @33
    @16
    @31
    @6
    c.0
    @12
    cI
    @13
    eqeq1
    ifbid
    eqeq12d
    @13
    cJ
    wceq
    #
    @30
    @4
    @32
    @7
    @13
    cJ
    cI
    cM
    oveq2
    @34
    @31
    @5
    @6
    c.0
    @13
    cJ
    cI
    eqeq2
    ifbid
    eqeq12d
    rspc2v
    reximdv
    com12
    adantl
    a1i
    syl5bi
    sylbid
    ex
    3imp1
end
