include "c0.mm"
include "wne.mm"
include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cui.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cotp.mm"
include "cmmul.mm"
include "cbs.mm"
include "eqid.mm"
include "crg.mm"
include "crngring.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "cmap.mm"
include "anim2i.mm"
include "anim1i.mm"
include "3adant3.mm"
include "simpr.mm"
include "3ad2ant3.mm"
include "slesolvec.mm"
include "sylc.mm"
include "syl6eleq.mm"
include "anim12ci.mm"
include "matring.mm"
include "syl.mm"
include "wb.mm"
include "matunit.mm"
include "bicomd.mm"
include "ad2ant2lr.mm"
include "biimpd.mm"
include "adantrd.mm"
include "3impia.mm"
include "ringinvcl.mm"
include "syl2anc.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "mavmulass.mm"
include "cur.mm"
include "cmulr.mm"
include "matmulr.mm"
include "oveqd.mm"
include "unitlinv.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "1mavmul.mm"
include "oveq2.mm"
include "3eqtr3d.mm"

theorem slesolinv
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume slesolex.a: |- A = ( N Mat R )
  assume slesolex.b: |- B = ( Base ` A )
  assume slesolex.v: |- V = ( ( Base ` R ) ^m N )
  assume slesolex.x: |- .x. = ( R maVecMul <. N , N >. )
  assume slesolex.d: |- D = ( N maDet R )
  assume slesolinv.i: |- I = ( invr ` A )


  assert |- ( ( ( N =/= (/) /\ R e. CRing ) /\ ( X e. B /\ Y e. V ) /\ ( ( D ` X ) e. ( Unit ` R ) /\ ( X .x. Z ) = Y ) ) -> Z = ( ( I ` X ) .x. Y ) )

  proof
    cN
    c0
    wne
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    cX
    cD
    cfv
    cR
    cui
    cfv
    #
    wcel
    #
    cX
    cZ
    c.x
    co
    #
    cY
    wceq
    #
    wa
    #
    w3a
    #
    cX
    cI
    cfv
    #
    cX
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    #
    cZ
    c.x
    co
    #
    @12
    @8
    c.x
    co
    #
    cZ
    @12
    cY
    c.x
    co
    #
    @11
    cA
    cR
    cbs
    cfv
    #
    cR
    c.x
    @13
    cN
    @12
    cZ
    cX
    slesolex.a
    @18
    eqid
    #
    slesolex.x
    @2
    @5
    cR
    crg
    wcel
    #
    @10
    @1
    @20
    @0
    cR
    crngring
    #
    adantl
    #
    3ad2ant1
    #
    @5
    @2
    cN
    cfn
    wcel
    #
    @10
    @3
    @24
    @4
    @3
    @24
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cX
    slesolex.a
    slesolex.b
    matrcl
    simpld
    adantr
    #
    3ad2ant2
    #
    @11
    cZ
    cV
    @18
    cN
    cmap
    co
    @11
    @0
    @20
    wa
    #
    @5
    wa
    #
    @9
    cZ
    cV
    wcel
    @2
    @5
    @28
    @10
    @2
    @27
    @5
    @1
    @20
    @0
    @21
    anim2i
    anim1i
    3adant3
    @10
    @2
    @9
    @5
    @7
    @9
    simpr
    3ad2ant3
    cA
    cB
    cR
    c.x
    cN
    cV
    cX
    cY
    cZ
    slesolex.a
    slesolex.b
    slesolex.v
    slesolex.x
    slesolvec
    sylc
    slesolex.v
    syl6eleq
    #
    @13
    eqid
    #
    @11
    cA
    crg
    wcel
    #
    cX
    cA
    cui
    cfv
    #
    wcel
    #
    @12
    cA
    cbs
    cfv
    #
    wcel
    @11
    @24
    @20
    wa
    #
    @31
    @2
    @5
    @35
    @10
    @2
    @20
    @5
    @24
    @22
    @25
    anim12ci
    3adant3
    cA
    cR
    cN
    slesolex.a
    matring
    syl
    #
    @2
    @5
    @10
    @33
    @2
    @5
    wa
    #
    @7
    @33
    @9
    @37
    @7
    @33
    @1
    @3
    @7
    @33
    wb
    @0
    @4
    @1
    @3
    wa
    @33
    @7
    cA
    cB
    cD
    cR
    @32
    cX
    cN
    @6
    slesolex.a
    slesolex.d
    slesolex.b
    @32
    eqid
    #
    @6
    eqid
    matunit
    bicomd
    ad2ant2lr
    biimpd
    adantrd
    3impia
    #
    @34
    cA
    @32
    cI
    cX
    @38
    slesolinv.i
    @34
    eqid
    ringinvcl
    syl2anc
    @5
    @2
    cX
    @34
    wcel
    #
    @10
    @3
    @40
    @4
    @3
    @40
    cB
    @34
    cX
    slesolex.b
    eleq2i
    biimpi
    adantr
    3ad2ant2
    mavmulass
    @11
    @15
    cA
    cur
    cfv
    #
    cZ
    c.x
    co
    cZ
    @11
    @14
    @41
    cZ
    c.x
    @11
    @14
    @12
    cX
    cA
    cmulr
    cfv
    #
    co
    #
    @41
    @11
    @13
    @42
    @12
    cX
    @11
    @24
    @1
    wa
    #
    @13
    @42
    wceq
    @2
    @5
    @44
    @10
    @2
    @1
    @5
    @24
    @0
    @1
    simpr
    @25
    anim12ci
    3adant3
    cA
    cR
    @13
    cN
    ccrg
    slesolex.a
    @30
    matmulr
    syl
    oveqd
    @11
    @31
    @33
    @43
    @41
    wceq
    @36
    @39
    cA
    @42
    @32
    @41
    cI
    cX
    @38
    slesolinv.i
    @42
    eqid
    @41
    eqid
    unitlinv
    syl2anc
    eqtrd
    oveq1d
    @11
    cA
    @18
    cR
    c.x
    cN
    cZ
    slesolex.a
    @19
    slesolex.x
    @23
    @26
    @29
    1mavmul
    eqtrd
    @10
    @2
    @16
    @17
    wceq
    #
    @5
    @9
    @45
    @7
    @8
    cY
    @12
    c.x
    oveq2
    adantl
    3ad2ant3
    3eqtr3d
end
