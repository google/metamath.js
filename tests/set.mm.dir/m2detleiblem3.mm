include "crg.mm"
include "wcel.mm"
include "c1.mm"
include "cop.mm"
include "c2.mm"
include "cpr.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "mgpbas.mm"
include "cmgp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wral.mm"
include "wf.mm"
include "cn.mm"
include "1ex.mm"
include "2nn.mm"
include "wa.mm"
include "prex.mm"
include "prid1.mm"
include "csymg.mm"
include "symg2bas.mm"
include "syl5eleqr.mm"
include "mp2an.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "cmat.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "matepmcl.mm"
include "syl3an2.mm"
include "mpteq1.mm"
include "ax-mp.mm"
include "fmpt.mm"
include "sylib.mm"
include "gsumpr12val.mm"
include "eleqtrri.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "rspcva.mm"
include "sylancr.mm"
include "fvmptg.mm"
include "fveq1.mm"
include "wne.mm"
include "1ne2.mm"
include "fvpr1.mm"
include "syl6eq.mm"
include "3ad2ant2.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "2ex.mm"
include "prid2.mm"
include "fvpr2.mm"

theorem m2detleiblem3
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let vn: setvar n
  let cG: class G
  let cM: class M
  let cN: class N
  assume m2detleiblem2.n: |- N = { 1 , 2 }
  assume m2detleiblem2.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume m2detleiblem2.a: |- A = ( N Mat R )
  assume m2detleiblem2.b: |- B = ( Base ` A )
  assume m2detleiblem2.g: |- G = ( mulGrp ` R )
  assume m2detleiblem3.m: |- .x. = ( +g ` G )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint Q n
  disjoint R n
  assert |- ( ( R e. Ring /\ Q = { <. 1 , 1 >. , <. 2 , 2 >. } /\ M e. B ) -> ( G gsum ( n e. N |-> ( ( Q ` n ) M n ) ) ) = ( ( 1 M 1 ) .x. ( 2 M 2 ) ) )

  proof
    cR
    crg
    wcel
    #
    cQ
    c1
    c1
    cop
    #
    c2
    c2
    cop
    #
    cpr
    #
    wceq
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cG
    vn
    cN
    vn
    cv
    #
    cQ
    cfv
    #
    @7
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    c1
    @10
    cfv
    #
    c2
    @10
    cfv
    #
    c.x
    co
    c1
    c1
    cM
    co
    #
    c2
    c2
    cM
    co
    #
    c.x
    co
    @6
    cR
    cbs
    cfv
    #
    c.x
    @10
    cG
    cvv
    @15
    cR
    cG
    m2detleiblem2.g
    @15
    eqid
    mgpbas
    m2detleiblem3.m
    cG
    cvv
    wcel
    @6
    cG
    cR
    cmgp
    cfv
    cvv
    m2detleiblem2.g
    cR
    cmgp
    fvex
    eqeltri
    a1i
    @6
    @9
    @15
    wcel
    #
    vn
    c1
    c2
    cpr
    #
    wral
    #
    @17
    @15
    @10
    wf
    @4
    @0
    cQ
    cP
    wcel
    #
    @5
    @18
    @4
    @19
    @3
    cP
    wcel
    #
    c1
    cvv
    wcel
    #
    c2
    cn
    wcel
    #
    @20
    1ex
    2nn
    @21
    @22
    wa
    @3
    @3
    c1
    c2
    cop
    c2
    c1
    cop
    cpr
    #
    cpr
    cP
    @3
    @23
    @1
    @2
    prex
    prid1
    cN
    cP
    cN
    csymg
    cfv
    #
    c1
    c2
    cvv
    cn
    @24
    eqid
    m2detleiblem2.p
    m2detleiblem2.n
    symg2bas
    syl5eleqr
    mp2an
    cQ
    @3
    cP
    eleq1
    mpbiri
    #
    cA
    cB
    cP
    cQ
    cR
    vn
    cM
    @17
    cA
    cN
    cR
    cmat
    co
    @17
    cR
    cmat
    co
    m2detleiblem2.a
    cN
    @17
    cR
    cmat
    m2detleiblem2.n
    oveq1i
    eqtri
    m2detleiblem2.b
    cP
    @24
    cbs
    cfv
    @17
    csymg
    cfv
    #
    cbs
    cfv
    m2detleiblem2.p
    @24
    @26
    cbs
    cN
    @17
    csymg
    m2detleiblem2.n
    fveq2i
    fveq2i
    eqtri
    matepmcl
    syl3an2
    vn
    @17
    @15
    @9
    @10
    cN
    @17
    wceq
    @10
    vn
    @17
    @9
    cmpt
    wceq
    m2detleiblem2.n
    vn
    cN
    @17
    @9
    mpteq1
    ax-mp
    fmpt
    sylib
    gsumpr12val
    @6
    @11
    @13
    @12
    @14
    c.x
    @6
    @11
    c1
    cQ
    cfv
    #
    c1
    cM
    co
    #
    @13
    @6
    c1
    cN
    wcel
    #
    @28
    @15
    wcel
    #
    @11
    @28
    wceq
    c1
    @17
    cN
    c1
    c2
    1ex
    prid1
    m2detleiblem2.n
    eleqtrri
    #
    @6
    @29
    @16
    vn
    cN
    wral
    #
    @30
    @31
    @4
    @0
    @19
    @5
    @32
    @25
    cA
    cB
    cP
    cQ
    cR
    vn
    cM
    cN
    m2detleiblem2.a
    m2detleiblem2.b
    m2detleiblem2.p
    matepmcl
    syl3an2
    #
    @16
    @30
    vn
    c1
    cN
    @7
    c1
    wceq
    #
    @9
    @28
    @15
    @34
    @8
    @27
    @7
    c1
    cM
    @7
    c1
    cQ
    fveq2
    @34
    id
    oveq12d
    #
    eleq1d
    rspcva
    sylancr
    vn
    c1
    @9
    @28
    cN
    @15
    @10
    @35
    @10
    eqid
    #
    fvmptg
    sylancr
    @6
    @27
    c1
    c1
    cM
    @4
    @0
    @27
    c1
    wceq
    @5
    @4
    @27
    c1
    @3
    cfv
    #
    c1
    c1
    cQ
    @3
    fveq1
    c1
    c2
    wne
    #
    @37
    c1
    wceq
    1ne2
    c1
    c2
    c1
    c2
    1ex
    1ex
    fvpr1
    ax-mp
    syl6eq
    3ad2ant2
    oveq1d
    eqtrd
    @6
    @12
    c2
    cQ
    cfv
    #
    c2
    cM
    co
    #
    @14
    @6
    c2
    cN
    wcel
    #
    @40
    @15
    wcel
    #
    @12
    @40
    wceq
    c2
    @17
    cN
    c1
    c2
    2ex
    prid2
    m2detleiblem2.n
    eleqtrri
    #
    @6
    @41
    @32
    @42
    @43
    @33
    @16
    @42
    vn
    c2
    cN
    @7
    c2
    wceq
    #
    @9
    @40
    @15
    @44
    @8
    @39
    @7
    c2
    cM
    @7
    c2
    cQ
    fveq2
    @44
    id
    oveq12d
    #
    eleq1d
    rspcva
    sylancr
    vn
    c2
    @9
    @40
    cN
    @15
    @10
    @45
    @36
    fvmptg
    sylancr
    @6
    @39
    c2
    c2
    cM
    @4
    @0
    @39
    c2
    wceq
    @5
    @4
    @39
    c2
    @3
    cfv
    #
    c2
    c2
    cQ
    @3
    fveq1
    @38
    @46
    c2
    wceq
    1ne2
    c1
    c2
    c1
    c2
    2ex
    2ex
    fvpr2
    ax-mp
    syl6eq
    3ad2ant2
    oveq1d
    eqtrd
    oveq12d
    eqtrd
end
