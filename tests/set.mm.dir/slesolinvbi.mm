include "c0.mm"
include "wne.mm"
include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cui.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simp3.mm"
include "anim1i.mm"
include "slesolinv.mm"
include "syl3anc.mm"
include "oveq2.mm"
include "cotp.mm"
include "cmmul.mm"
include "cur.mm"
include "cmulr.mm"
include "cfn.mm"
include "simpr.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantr.mm"
include "anim12ci.mm"
include "3adant3.mm"
include "eqid.mm"
include "matmulr.mm"
include "syl.mm"
include "oveqd.mm"
include "crg.mm"
include "crngring.mm"
include "adantl.mm"
include "matring.mm"
include "wb.mm"
include "matunit.mm"
include "ad2ant2lr.mm"
include "biimp3ar.mm"
include "unitrinv.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cbs.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "cmap.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "ringinvcl.mm"
include "mavmulass.mm"
include "1mavmul.mm"
include "3eqtr3d.mm"
include "sylan9eqr.mm"
include "impbida.mm"

theorem slesolinvbi
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


  assert |- ( ( ( N =/= (/) /\ R e. CRing ) /\ ( X e. B /\ Y e. V ) /\ ( D ` X ) e. ( Unit ` R ) ) -> ( ( X .x. Z ) = Y <-> Z = ( ( I ` X ) .x. Y ) ) )

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
    w3a
    #
    cX
    cZ
    c.x
    co
    #
    cY
    wceq
    #
    cZ
    cX
    cI
    cfv
    #
    cY
    c.x
    co
    #
    wceq
    #
    @8
    @10
    wa
    @2
    @5
    @7
    @10
    wa
    @13
    @2
    @5
    @7
    @10
    simpl1
    @2
    @5
    @7
    @10
    simpl2
    @8
    @7
    @10
    @2
    @5
    @7
    simp3
    anim1i
    cA
    cB
    cD
    cR
    c.x
    cI
    cN
    cV
    cX
    cY
    cZ
    slesolex.a
    slesolex.b
    slesolex.v
    slesolex.x
    slesolex.d
    slesolinv.i
    slesolinv
    syl3anc
    @13
    @8
    @9
    cX
    @12
    c.x
    co
    #
    cY
    cZ
    @12
    cX
    c.x
    oveq2
    @8
    cX
    @11
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
    cY
    c.x
    co
    cA
    cur
    cfv
    #
    cY
    c.x
    co
    @14
    cY
    @8
    @16
    @17
    cY
    c.x
    @8
    @16
    cX
    @11
    cA
    cmulr
    cfv
    #
    co
    #
    @17
    @8
    @15
    @18
    cX
    @11
    @8
    cN
    cfn
    wcel
    #
    @1
    wa
    #
    @15
    @18
    wceq
    @2
    @5
    @21
    @7
    @2
    @1
    @5
    @20
    @0
    @1
    simpr
    @3
    @20
    @4
    @3
    @20
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
    anim12ci
    3adant3
    cA
    cR
    @15
    cN
    ccrg
    slesolex.a
    @15
    eqid
    #
    matmulr
    syl
    oveqd
    @8
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
    @19
    @17
    wceq
    @8
    @20
    cR
    crg
    wcel
    #
    wa
    #
    @24
    @2
    @5
    @28
    @7
    @2
    @27
    @5
    @20
    @1
    @27
    @0
    cR
    crngring
    adantl
    #
    @22
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
    @26
    @7
    @1
    @3
    @26
    @7
    wb
    @0
    @4
    cA
    cB
    cD
    cR
    @25
    cX
    cN
    @6
    slesolex.a
    slesolex.d
    slesolex.b
    @25
    eqid
    #
    @6
    eqid
    matunit
    ad2ant2lr
    biimp3ar
    #
    cA
    @18
    @25
    @17
    cI
    cX
    @31
    slesolinv.i
    @18
    eqid
    @17
    eqid
    unitrinv
    syl2anc
    eqtrd
    oveq1d
    @8
    cA
    cR
    cbs
    cfv
    #
    cR
    c.x
    @15
    cN
    cX
    cY
    @11
    slesolex.a
    @33
    eqid
    #
    slesolex.x
    @2
    @5
    @27
    @7
    @29
    3ad2ant1
    #
    @5
    @2
    @20
    @7
    @22
    3ad2ant2
    #
    @5
    @2
    cY
    @33
    cN
    cmap
    co
    #
    wcel
    #
    @7
    @4
    @38
    @3
    @4
    @38
    cV
    @37
    cY
    slesolex.v
    eleq2i
    biimpi
    adantl
    3ad2ant2
    #
    @23
    @5
    @2
    cX
    cA
    cbs
    cfv
    #
    wcel
    #
    @7
    @3
    @41
    @4
    @3
    @41
    cB
    @40
    cX
    slesolex.b
    eleq2i
    biimpi
    adantr
    3ad2ant2
    @8
    @24
    @26
    @11
    @40
    wcel
    @30
    @32
    @40
    cA
    @25
    cI
    cX
    @31
    slesolinv.i
    @40
    eqid
    ringinvcl
    syl2anc
    mavmulass
    @8
    cA
    @33
    cR
    c.x
    cN
    cY
    slesolex.a
    @34
    slesolex.x
    @35
    @36
    @39
    1mavmul
    3eqtr3d
    sylan9eqr
    impbida
end
