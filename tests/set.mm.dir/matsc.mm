include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cur.mm"
include "cfv.mm"
include "co.mm"
include "cxp.mm"
include "csn.mm"
include "cmulr.mm"
include "cof.mm"
include "weq.mm"
include "cif.mm"
include "cmpt2.mm"
include "cbs.mm"
include "wceq.mm"
include "simp3.mm"
include "wa.mm"
include "3simpa.mm"
include "matring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "3syl.mm"
include "matvsca2.mm"
include "syl2anc.mm"
include "cvv.mm"
include "simp1.mm"
include "cv.mm"
include "simp13.mm"
include "fvex.mm"
include "c0g.mm"
include "eqeltri.mm"
include "ifex.mm"
include "a1i.mm"
include "fconstmpt2.mm"
include "mat1.mm"
include "3adant3.mm"
include "offval22.mm"
include "ovif2.mm"
include "ringridm.mm"
include "3adant1.mm"
include "ringrz.mm"
include "ifeq12d.mm"
include "syl5eq.mm"
include "mpt2eq3dv.mm"
include "3eqtrd.mm"

theorem matsc
  let cA: class A
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cL: class L
  let cN: class N
  let c.0: class .0.
  assume matsc.a: |- A = ( N Mat R )
  assume matsc.k: |- K = ( Base ` R )
  assume matsc.m: |- .x. = ( .s ` A )
  assume matsc.z: |- .0. = ( 0g ` R )

  disjoint i j
  disjoint .0. i
  disjoint .0. j
  disjoint A i
  disjoint A j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint .x. i
  disjoint .x. j
  disjoint L i
  disjoint L j
  disjoint K i
  disjoint K j
  assert |- ( ( N e. Fin /\ R e. Ring /\ L e. K ) -> ( L .x. ( 1r ` A ) ) = ( i e. N , j e. N |-> if ( i = j , L , .0. ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cL
    cK
    wcel
    #
    w3a
    #
    cL
    cA
    cur
    cfv
    #
    c.x
    co
    #
    cN
    cN
    cxp
    #
    cL
    csn
    cxp
    #
    @4
    cR
    cmulr
    cfv
    #
    cof
    co
    #
    vi
    vj
    cN
    cN
    cL
    vi
    vj
    weq
    #
    cR
    cur
    cfv
    #
    c.0
    cif
    #
    @8
    co
    #
    cmpt2
    vi
    vj
    cN
    cN
    @10
    cL
    c.0
    cif
    #
    cmpt2
    @3
    @2
    @4
    cA
    cbs
    cfv
    #
    wcel
    #
    @5
    @9
    wceq
    @0
    @1
    @2
    simp3
    @3
    @0
    @1
    wa
    cA
    crg
    wcel
    @16
    @0
    @1
    @2
    3simpa
    cA
    cR
    cN
    matsc.a
    matring
    @15
    cA
    @4
    @15
    eqid
    #
    @4
    eqid
    ringidcl
    3syl
    cA
    @15
    @6
    cR
    c.x
    @8
    cK
    cN
    cL
    @4
    matsc.a
    @17
    matsc.k
    matsc.m
    @8
    eqid
    #
    @6
    eqid
    matvsca2
    syl2anc
    @3
    vi
    vj
    cN
    cN
    cL
    @12
    @8
    @7
    @4
    cfn
    cfn
    cK
    cvv
    @0
    @1
    @2
    simp1
    #
    @19
    @0
    @1
    @2
    vi
    cv
    cN
    wcel
    #
    vj
    cv
    cN
    wcel
    #
    simp13
    @12
    cvv
    wcel
    @3
    @20
    @21
    w3a
    @10
    @11
    c.0
    cR
    cur
    fvex
    c.0
    cR
    c0g
    cfv
    cvv
    matsc.z
    cR
    c0g
    fvex
    eqeltri
    ifex
    a1i
    @7
    vi
    vj
    cN
    cN
    cL
    cmpt2
    wceq
    @3
    vi
    vj
    cN
    cN
    cL
    fconstmpt2
    a1i
    @0
    @1
    @4
    vi
    vj
    cN
    cN
    @12
    cmpt2
    wceq
    @2
    cA
    cR
    @11
    vi
    vj
    cN
    c.0
    matsc.a
    @11
    eqid
    #
    matsc.z
    mat1
    3adant3
    offval22
    @3
    vi
    vj
    cN
    cN
    @13
    @14
    @3
    @13
    @10
    cL
    @11
    @8
    co
    #
    cL
    c.0
    @8
    co
    #
    cif
    @14
    @10
    cL
    @11
    c.0
    @8
    ovif2
    @3
    @10
    @23
    cL
    @24
    c.0
    @1
    @2
    @23
    cL
    wceq
    @0
    cK
    cR
    @8
    @11
    cL
    matsc.k
    @18
    @22
    ringridm
    3adant1
    @1
    @2
    @24
    c.0
    wceq
    @0
    cK
    cR
    @8
    cL
    c.0
    matsc.k
    @18
    matsc.z
    ringrz
    3adant1
    ifeq12d
    syl5eq
    mpt2eq3dv
    3eqtrd
end
