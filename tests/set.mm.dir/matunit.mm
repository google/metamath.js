include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cinvr.mm"
include "wceq.mm"
include "cbs.mm"
include "cmulr.mm"
include "cur.mm"
include "eqid.mm"
include "crg.mm"
include "crngring.mm"
include "ad2antrr.mm"
include "mdetcl.mm"
include "adantr.mm"
include "wf.mm"
include "mdetf.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "ad2antlr.mm"
include "matring.mm"
include "syl2anc.mm"
include "ringinvcl.mm"
include "sylancom.mm"
include "ffvelrnd.mm"
include "co.mm"
include "unitrinv.mm"
include "fveq2d.mm"
include "simpll.mm"
include "simplr.mm"
include "mdetmul.mm"
include "syl3anc.mm"
include "mdet1.mm"
include "3eqtr3d.mm"
include "unitlinv.mm"
include "invrvald.mm"
include "w3a.mm"
include "cmadu.mm"
include "cvsca.mm"
include "matinv.mm"
include "3expa.mm"
include "impbida.mm"

theorem matunit
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cU: class U
  let cM: class M
  let cN: class N
  let cV: class V
  assume matunit.a: |- A = ( N Mat R )
  assume matunit.d: |- D = ( N maDet R )
  assume matunit.b: |- B = ( Base ` A )
  assume matunit.u: |- U = ( Unit ` A )
  assume matunit.v: |- V = ( Unit ` R )


  assert |- ( ( R e. CRing /\ M e. B ) -> ( M e. U <-> ( D ` M ) e. V ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    cM
    cU
    wcel
    #
    cM
    cD
    cfv
    #
    cV
    wcel
    #
    @2
    @3
    wa
    #
    @5
    @4
    cR
    cinvr
    cfv
    #
    cfv
    #
    cM
    cA
    cinvr
    cfv
    #
    cfv
    #
    cD
    cfv
    #
    wceq
    @6
    cR
    cbs
    cfv
    #
    cR
    cR
    cmulr
    cfv
    #
    cV
    cR
    cur
    cfv
    #
    @7
    @4
    @11
    @12
    eqid
    #
    @13
    eqid
    #
    @14
    eqid
    #
    matunit.v
    @7
    eqid
    #
    @0
    cR
    crg
    wcel
    #
    @1
    @3
    cR
    crngring
    ad2antrr
    #
    @2
    @4
    @12
    wcel
    @3
    cA
    cB
    cD
    cR
    @12
    cM
    cN
    matunit.d
    matunit.a
    matunit.b
    @15
    mdetcl
    adantr
    @6
    cB
    @12
    @10
    cD
    @0
    cB
    @12
    cD
    wf
    @1
    @3
    cA
    cB
    cD
    cR
    @12
    cN
    matunit.d
    matunit.a
    matunit.b
    @15
    mdetf
    ad2antrr
    @2
    @3
    cA
    crg
    wcel
    #
    @10
    cB
    wcel
    #
    @6
    cN
    cfn
    wcel
    #
    @19
    @21
    @1
    @23
    @0
    @3
    @1
    @23
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    matunit.a
    matunit.b
    matrcl
    simpld
    ad2antlr
    #
    @20
    cA
    cR
    cN
    matunit.a
    matring
    syl2anc
    #
    cB
    cA
    cU
    @9
    cM
    matunit.u
    @9
    eqid
    #
    matunit.b
    ringinvcl
    sylancom
    #
    ffvelrnd
    @6
    cM
    @10
    cA
    cmulr
    cfv
    #
    co
    #
    cD
    cfv
    #
    cA
    cur
    cfv
    #
    cD
    cfv
    #
    @4
    @11
    @13
    co
    #
    @14
    @6
    @29
    @31
    cD
    @2
    @3
    @21
    @29
    @31
    wceq
    @25
    cA
    @28
    cU
    @31
    @9
    cM
    matunit.u
    @26
    @28
    eqid
    #
    @31
    eqid
    #
    unitrinv
    sylancom
    fveq2d
    @6
    @0
    @1
    @22
    @30
    @33
    wceq
    @0
    @1
    @3
    simpll
    #
    @0
    @1
    @3
    simplr
    #
    @27
    cA
    cB
    cD
    cR
    @28
    @13
    cM
    @10
    cN
    matunit.a
    matunit.b
    matunit.d
    @16
    @34
    mdetmul
    syl3anc
    @6
    @0
    @23
    @32
    @14
    wceq
    @36
    @24
    cA
    cD
    cR
    @14
    @31
    cN
    matunit.d
    matunit.a
    @35
    @17
    mdet1
    syl2anc
    #
    3eqtr3d
    @6
    @10
    cM
    @28
    co
    #
    cD
    cfv
    #
    @32
    @11
    @4
    @13
    co
    #
    @14
    @6
    @39
    @31
    cD
    @2
    @3
    @21
    @39
    @31
    wceq
    @25
    cA
    @28
    cU
    @31
    @9
    cM
    matunit.u
    @26
    @34
    @35
    unitlinv
    sylancom
    fveq2d
    @6
    @0
    @22
    @1
    @40
    @41
    wceq
    @36
    @27
    @37
    cA
    cB
    cD
    cR
    @28
    @13
    @10
    cM
    cN
    matunit.a
    matunit.b
    matunit.d
    @16
    @34
    mdetmul
    syl3anc
    @38
    3eqtr3d
    invrvald
    simpld
    @0
    @1
    @5
    @3
    @0
    @1
    @5
    w3a
    @3
    @10
    @8
    cM
    cN
    cR
    cmadu
    co
    #
    cfv
    cA
    cvsca
    cfv
    #
    co
    wceq
    cA
    cB
    cD
    cR
    @43
    cU
    @7
    @9
    @42
    cM
    cN
    cV
    matunit.a
    @42
    eqid
    matunit.d
    matunit.b
    matunit.u
    matunit.v
    @18
    @26
    @43
    eqid
    matinv
    simpld
    3expa
    impbida
end
