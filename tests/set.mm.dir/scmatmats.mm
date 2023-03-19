include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "weq.mm"
include "cif.mm"
include "wral.mm"
include "eqid.mm"
include "scmatval.mm"
include "wb.mm"
include "simpr.mm"
include "adantr.mm"
include "simpll.mm"
include "matring.mm"
include "ringidcl.mm"
include "syl.mm"
include "anim1i.mm"
include "ancomd.mm"
include "matvscl.mm"
include "syl2anc.mm"
include "eqmat.mm"
include "w3a.mm"
include "simplll.mm"
include "simpllr.mm"
include "3jca.mm"
include "scmatscmide.mm"
include "sylan.mm"
include "eqeq2d.mm"
include "2ralbidva.mm"
include "bitrd.mm"
include "rexbidva.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem scmatmats
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let cK: class K
  let cN: class N
  let c.0: class .0.
  let vc: setvar c
  let cM: class M
  let cI: class I
  let cJ: class J
  assume scmatmat.a: |- A = ( N Mat R )
  assume scmatmat.b: |- B = ( Base ` A )
  assume scmatmat.s: |- S = ( N ScMat R )
  assume scmate.k: |- K = ( Base ` R )
  assume scmate.0: |- .0. = ( 0g ` R )

  disjoint N c
  disjoint R c
  disjoint K c
  disjoint S c
  disjoint A i
  disjoint A j
  disjoint i j
  disjoint B c
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
  disjoint M c
  disjoint M m
  disjoint I c
  disjoint J c
  assert |- ( ( N e. Fin /\ R e. Ring ) -> S = { m e. B | E. c e. K A. i e. N A. j e. N ( i m j ) = if ( i = j , c , .0. ) } )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cS
    vm
    cv
    #
    vc
    cv
    #
    cA
    cur
    cfv
    #
    cA
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vc
    cK
    wrex
    #
    vm
    cB
    crab
    vi
    cv
    #
    vj
    cv
    #
    @3
    co
    #
    vi
    vj
    weq
    @4
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
    cA
    cB
    cR
    cS
    @6
    @5
    vm
    cK
    cN
    crg
    vc
    scmate.k
    scmatmat.a
    scmatmat.b
    @5
    eqid
    #
    @6
    eqid
    #
    scmatmat.s
    scmatval
    @2
    @9
    @16
    vm
    cB
    @2
    @3
    cB
    wcel
    #
    wa
    #
    @8
    @15
    vc
    cK
    @20
    @4
    cK
    wcel
    #
    wa
    #
    @8
    @12
    @10
    @11
    @7
    co
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
    @15
    @22
    @19
    @7
    cB
    wcel
    #
    @8
    @25
    wb
    @20
    @19
    @21
    @2
    @19
    simpr
    adantr
    @22
    @2
    @21
    @5
    cB
    wcel
    #
    wa
    @26
    @2
    @19
    @21
    simpll
    @22
    @27
    @21
    @20
    @27
    @21
    @2
    @27
    @19
    @2
    cA
    crg
    wcel
    @27
    cA
    cR
    cN
    scmatmat.a
    matring
    cB
    cA
    @5
    scmatmat.b
    @17
    ringidcl
    syl
    adantr
    anim1i
    ancomd
    cA
    cB
    @4
    cR
    @6
    cK
    cN
    @5
    scmate.k
    scmatmat.a
    scmatmat.b
    @18
    matvscl
    syl2anc
    cA
    cB
    cR
    vi
    vj
    cN
    @3
    @7
    scmatmat.a
    scmatmat.b
    eqmat
    syl2anc
    @22
    @24
    @14
    vi
    vj
    cN
    cN
    @22
    @10
    cN
    wcel
    @11
    cN
    wcel
    wa
    #
    wa
    @23
    @13
    @12
    @22
    @0
    @1
    @21
    w3a
    @28
    @23
    @13
    wceq
    @22
    @0
    @1
    @21
    @0
    @1
    @19
    @21
    simplll
    @0
    @1
    @19
    @21
    simpllr
    @20
    @21
    simpr
    3jca
    cA
    cK
    @4
    cR
    @5
    @10
    @6
    @11
    cN
    c.0
    scmatmat.a
    scmate.k
    scmate.0
    @17
    @18
    scmatscmide
    sylan
    eqeq2d
    2ralbidva
    bitrd
    rexbidva
    rabbidva
    eqtrd
end
