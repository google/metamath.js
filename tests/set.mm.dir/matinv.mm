include "ccrg.mm"
include "wcel.mm"
include "cfv.mm"
include "w3a.mm"
include "cmulr.mm"
include "cur.mm"
include "co.mm"
include "eqid.mm"
include "casa.mm"
include "crg.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "matassa.mm"
include "syl2anc.mm"
include "assaring.mm"
include "syl.mm"
include "simp2.mm"
include "clmod.mm"
include "csca.mm"
include "cbs.mm"
include "assalmod.mm"
include "crngring.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "ringinvcl.mm"
include "wceq.mm"
include "matsca2.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "wf.mm"
include "maduf.mm"
include "ffvelrnd.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "assaassr.mm"
include "syl13anc.mm"
include "madurid.mm"
include "oveq2d.mm"
include "unitlinv.mm"
include "oveqd.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"
include "unitcl.mm"
include "3ad2ant3.mm"
include "ringidcl.mm"
include "lmodvsass.mm"
include "lmodvs1.mm"
include "3eqtrd.mm"
include "assaass.mm"
include "madulid.mm"
include "invrvald.mm"

theorem matinv
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.xb: class .xb
  let cU: class U
  let cH: class H
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cV: class V
  assume matinv.a: |- A = ( N Mat R )
  assume matinv.j: |- J = ( N maAdju R )
  assume matinv.d: |- D = ( N maDet R )
  assume matinv.b: |- B = ( Base ` A )
  assume matinv.u: |- U = ( Unit ` A )
  assume matinv.v: |- V = ( Unit ` R )
  assume matinv.h: |- H = ( invr ` R )
  assume matinv.i: |- I = ( invr ` A )
  assume matinv.t: |- .xb = ( .s ` A )


  assert |- ( ( R e. CRing /\ M e. B /\ ( D ` M ) e. V ) -> ( M e. U /\ ( I ` M ) = ( ( H ` ( D ` M ) ) .xb ( J ` M ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    cM
    cD
    cfv
    #
    cV
    wcel
    #
    w3a
    #
    cB
    cA
    cA
    cmulr
    cfv
    #
    cU
    cA
    cur
    cfv
    #
    cI
    cM
    @2
    cH
    cfv
    #
    cM
    cJ
    cfv
    #
    c.xb
    co
    #
    matinv.b
    @5
    eqid
    #
    @6
    eqid
    #
    matinv.u
    matinv.i
    @4
    cA
    casa
    wcel
    #
    cA
    crg
    wcel
    #
    @4
    cN
    cfn
    wcel
    #
    @0
    @12
    @1
    @0
    @14
    @3
    @1
    @14
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    matinv.a
    matinv.b
    matrcl
    simpld
    3ad2ant2
    #
    @0
    @1
    @3
    simp1
    #
    cA
    cR
    cN
    matinv.a
    matassa
    syl2anc
    #
    cA
    assaring
    syl
    #
    @0
    @1
    @3
    simp2
    #
    @4
    cA
    clmod
    wcel
    #
    @7
    cA
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @8
    cB
    wcel
    #
    @9
    cB
    wcel
    @4
    @12
    @20
    @17
    cA
    assalmod
    syl
    #
    @4
    @7
    cR
    cbs
    cfv
    #
    @22
    @4
    cR
    crg
    wcel
    #
    @3
    @7
    @26
    wcel
    @0
    @1
    @27
    @3
    cR
    crngring
    3ad2ant1
    #
    @0
    @1
    @3
    simp3
    #
    @26
    cR
    cV
    cH
    @2
    matinv.v
    matinv.h
    @26
    eqid
    #
    ringinvcl
    syl2anc
    @4
    cR
    @21
    cbs
    @4
    @14
    @0
    cR
    @21
    wceq
    @15
    @16
    cA
    cR
    cN
    ccrg
    matinv.a
    matsca2
    syl2anc
    #
    fveq2d
    #
    eleqtrd
    #
    @4
    cB
    cB
    cM
    cJ
    @0
    @1
    cB
    cB
    cJ
    wf
    @3
    cA
    cB
    cR
    cJ
    cN
    matinv.a
    matinv.j
    matinv.b
    maduf
    3ad2ant1
    @19
    ffvelrnd
    #
    @7
    c.xb
    @21
    @22
    cB
    cA
    @8
    matinv.b
    @21
    eqid
    #
    matinv.t
    @22
    eqid
    #
    lmodvscl
    syl3anc
    @4
    cM
    @9
    @5
    co
    #
    @7
    cM
    @8
    @5
    co
    #
    c.xb
    co
    #
    @7
    @2
    @6
    c.xb
    co
    #
    c.xb
    co
    #
    @6
    @4
    @12
    @23
    @1
    @24
    @37
    @39
    wceq
    @17
    @33
    @19
    @34
    @7
    @22
    c.xb
    @5
    @21
    cB
    cA
    cM
    @8
    matinv.b
    @35
    @36
    matinv.t
    @10
    assaassr
    syl13anc
    @4
    @38
    @40
    @7
    c.xb
    @4
    @1
    @0
    @38
    @40
    wceq
    @19
    @16
    cA
    cB
    cD
    cR
    c.xb
    @5
    @6
    cJ
    cM
    cN
    matinv.a
    matinv.b
    matinv.j
    matinv.d
    @11
    @10
    matinv.t
    madurid
    syl2anc
    oveq2d
    @4
    @7
    @2
    @21
    cmulr
    cfv
    #
    co
    #
    @6
    c.xb
    co
    #
    @21
    cur
    cfv
    #
    @6
    c.xb
    co
    #
    @41
    @6
    @4
    @43
    @45
    @6
    c.xb
    @4
    @7
    @2
    cR
    cmulr
    cfv
    #
    co
    #
    cR
    cur
    cfv
    #
    @43
    @45
    @4
    @27
    @3
    @48
    @49
    wceq
    @28
    @29
    cR
    @47
    cV
    @49
    cH
    @2
    matinv.v
    matinv.h
    @47
    eqid
    @49
    eqid
    unitlinv
    syl2anc
    @4
    @47
    @42
    @7
    @2
    @4
    cR
    @21
    cmulr
    @31
    fveq2d
    oveqd
    @4
    cR
    @21
    cur
    @31
    fveq2d
    3eqtr3d
    oveq1d
    @4
    @20
    @23
    @2
    @22
    wcel
    @6
    cB
    wcel
    #
    @44
    @41
    wceq
    @25
    @33
    @4
    @2
    @26
    @22
    @3
    @0
    @2
    @26
    wcel
    @1
    @26
    cR
    cV
    @2
    @30
    matinv.v
    unitcl
    3ad2ant3
    @32
    eleqtrd
    @4
    @13
    @50
    @18
    cB
    cA
    @6
    matinv.b
    @11
    ringidcl
    syl
    #
    @7
    @2
    c.xb
    @42
    @21
    @22
    cB
    cA
    @6
    matinv.b
    @35
    matinv.t
    @36
    @42
    eqid
    lmodvsass
    syl13anc
    @4
    @20
    @50
    @46
    @6
    wceq
    @25
    @51
    c.xb
    @45
    @21
    cB
    cA
    @6
    matinv.b
    @35
    matinv.t
    @45
    eqid
    lmodvs1
    syl2anc
    3eqtr3d
    #
    3eqtrd
    @4
    @9
    cM
    @5
    co
    #
    @7
    @8
    cM
    @5
    co
    #
    c.xb
    co
    #
    @41
    @6
    @4
    @12
    @23
    @24
    @1
    @53
    @55
    wceq
    @17
    @33
    @34
    @19
    @7
    @22
    c.xb
    @5
    @21
    cB
    cA
    @8
    cM
    matinv.b
    @35
    @36
    matinv.t
    @10
    assaass
    syl13anc
    @4
    @54
    @40
    @7
    c.xb
    @4
    @1
    @0
    @54
    @40
    wceq
    @19
    @16
    cA
    cB
    cD
    cR
    c.xb
    @5
    @6
    cJ
    cM
    cN
    matinv.a
    matinv.b
    matinv.j
    matinv.d
    @11
    @10
    matinv.t
    madulid
    syl2anc
    oveq2d
    @52
    3eqtrd
    invrvald
end
