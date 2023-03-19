include "c0.mm"
include "wne.mm"
include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cui.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cinvr.mm"
include "cbs.mm"
include "cmap.mm"
include "cmulr.mm"
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
include "anim12ci.mm"
include "3adant3.mm"
include "matring.mm"
include "syl.mm"
include "wb.mm"
include "matunit.mm"
include "bicomd.mm"
include "ad2ant2lr.mm"
include "biimp3a.mm"
include "ringinvcl.mm"
include "syl2anc.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "mavmulcl.mm"
include "syl6eleqr.mm"
include "slesolinvbi.mm"
include "biimprd.mm"
include "impancom.mm"
include "rspcimedv.mm"
include "pm2.43i.mm"

theorem slesolex
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  assume slesolex.a: |- A = ( N Mat R )
  assume slesolex.b: |- B = ( Base ` A )
  assume slesolex.v: |- V = ( ( Base ` R ) ^m N )
  assume slesolex.x: |- .x. = ( R maVecMul <. N , N >. )
  assume slesolex.d: |- D = ( N maDet R )

  disjoint A z
  disjoint B z
  disjoint D z
  disjoint N z
  disjoint R z
  disjoint V z
  disjoint X z
  disjoint Y z
  disjoint .x. z
  assert |- ( ( ( N =/= (/) /\ R e. CRing ) /\ ( X e. B /\ Y e. V ) /\ ( D ` X ) e. ( Unit ` R ) ) -> E. z e. V ( X .x. z ) = Y )

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
    vz
    cv
    #
    c.x
    co
    cY
    wceq
    #
    vz
    cV
    wrex
    @8
    @10
    @8
    vz
    cX
    cA
    cinvr
    cfv
    #
    cfv
    #
    cY
    c.x
    co
    #
    cV
    @8
    @13
    cR
    cbs
    cfv
    #
    cN
    cmap
    co
    #
    cV
    @8
    cA
    @14
    cR
    cR
    cmulr
    cfv
    #
    c.x
    cN
    @12
    cY
    slesolex.a
    slesolex.x
    @14
    eqid
    @16
    eqid
    @2
    @5
    cR
    crg
    wcel
    #
    @7
    @1
    @17
    @0
    cR
    crngring
    adantl
    #
    3ad2ant1
    @5
    @2
    cN
    cfn
    wcel
    #
    @7
    @3
    @19
    @4
    @3
    @19
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
    @12
    cA
    cbs
    cfv
    #
    wcel
    @8
    @19
    @17
    wa
    #
    @21
    @2
    @5
    @25
    @7
    @2
    @17
    @5
    @19
    @18
    @20
    anim12ci
    3adant3
    cA
    cR
    cN
    slesolex.a
    matring
    syl
    @2
    @5
    @7
    @23
    @1
    @3
    @7
    @23
    wb
    @0
    @4
    @1
    @3
    wa
    @23
    @7
    cA
    cB
    cD
    cR
    @22
    cX
    cN
    @6
    slesolex.a
    slesolex.d
    slesolex.b
    @22
    eqid
    #
    @6
    eqid
    matunit
    bicomd
    ad2ant2lr
    biimp3a
    @24
    cA
    @22
    @11
    cX
    @26
    @11
    eqid
    #
    @24
    eqid
    ringinvcl
    syl2anc
    @5
    @2
    cY
    @15
    wcel
    #
    @7
    @4
    @28
    @3
    @4
    @28
    cV
    @15
    cY
    slesolex.v
    eleq2i
    biimpi
    adantl
    3ad2ant2
    mavmulcl
    slesolex.v
    syl6eleqr
    @8
    @8
    @9
    @13
    wceq
    #
    @10
    @8
    @8
    wa
    @10
    @29
    @8
    @10
    @29
    wb
    @8
    cA
    cB
    cD
    cR
    c.x
    @11
    cN
    cV
    cX
    cY
    @9
    slesolex.a
    slesolex.b
    slesolex.v
    slesolex.x
    slesolex.d
    @27
    slesolinvbi
    adantr
    biimprd
    impancom
    rspcimedv
    pm2.43i
end
