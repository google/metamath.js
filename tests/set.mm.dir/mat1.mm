include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "cbs.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "cur.mm"
include "cxp.mm"
include "cmap.mm"
include "eqid.mm"
include "simpr.mm"
include "simpl.mm"
include "mamumat1cl.mm"
include "matbas2.mm"
include "eleqtrd.mm"
include "cotp.mm"
include "cmmul.mm"
include "matmulr.mm"
include "adantr.mm"
include "oveqd.mm"
include "simplr.mm"
include "simpll.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "mamulid.mm"
include "eqtr3d.mm"
include "mamurid.mm"
include "jca.mm"
include "ralrimiva.mm"
include "wb.mm"
include "matring.mm"
include "isringid.mm"
include "syl.mm"
include "mpbi2and.mm"

theorem mat1
  let cA: class A
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let cN: class N
  let c.0: class .0.
  let vx: setvar x
  assume mat1.a: |- A = ( N Mat R )
  assume mat1.o: |- .1. = ( 1r ` R )
  assume mat1.z: |- .0. = ( 0g ` R )

  disjoint i j
  disjoint .0. i
  disjoint .0. j
  disjoint .1. i
  disjoint .1. j
  disjoint A i
  disjoint A j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint i x
  disjoint j x
  disjoint .0. x
  disjoint .1. x
  disjoint A x
  disjoint N x
  disjoint R x
  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( 1r ` A ) = ( i e. N , j e. N |-> if ( i = j , .1. , .0. ) ) )

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
    vi
    vj
    cN
    cN
    vi
    cv
    vj
    cv
    wceq
    c.1
    c.0
    cif
    cmpt2
    #
    cA
    cbs
    cfv
    #
    wcel
    #
    @3
    vx
    cv
    #
    cA
    cmulr
    cfv
    #
    co
    #
    @6
    wceq
    #
    @6
    @3
    @7
    co
    #
    @6
    wceq
    #
    wa
    #
    vx
    @4
    wral
    #
    cA
    cur
    cfv
    #
    @3
    wceq
    #
    @2
    @3
    cR
    cbs
    cfv
    #
    cN
    cN
    cxp
    cmap
    co
    #
    @4
    @2
    @16
    cR
    c.1
    vi
    vj
    @3
    cN
    c.0
    @16
    eqid
    #
    @0
    @1
    simpr
    mat1.o
    mat1.z
    @3
    eqid
    #
    @0
    @1
    simpl
    mamumat1cl
    cA
    cR
    @16
    cN
    crg
    mat1.a
    @18
    matbas2
    #
    eleqtrd
    @2
    @12
    vx
    @4
    @2
    @6
    @4
    wcel
    #
    wa
    #
    @9
    @11
    @22
    @3
    @6
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    @8
    @6
    @22
    @23
    @7
    @3
    @6
    @2
    @23
    @7
    wceq
    @21
    cA
    cR
    @23
    cN
    crg
    mat1.a
    @23
    eqid
    #
    matmulr
    adantr
    #
    oveqd
    @22
    @16
    cR
    c.1
    vi
    vj
    @23
    @3
    cN
    cN
    @6
    c.0
    @18
    @0
    @1
    @21
    simplr
    #
    mat1.o
    mat1.z
    @19
    @0
    @1
    @21
    simpll
    #
    @27
    @24
    @2
    @6
    @17
    wcel
    @21
    @2
    @17
    @4
    @6
    @20
    eleq2d
    biimpar
    #
    mamulid
    eqtr3d
    @22
    @6
    @3
    @23
    co
    @10
    @6
    @22
    @23
    @7
    @6
    @3
    @25
    oveqd
    @22
    @16
    cR
    c.1
    vi
    vj
    @23
    @3
    cN
    cN
    @6
    c.0
    @18
    @26
    mat1.o
    mat1.z
    @19
    @27
    @27
    @24
    @28
    mamurid
    eqtr3d
    jca
    ralrimiva
    @2
    cA
    crg
    wcel
    @5
    @13
    wa
    @15
    wb
    cA
    cR
    cN
    mat1.a
    matring
    vx
    @4
    cA
    @7
    @14
    @3
    @4
    eqid
    @7
    eqid
    @14
    eqid
    isringid
    syl
    mpbi2and
end
