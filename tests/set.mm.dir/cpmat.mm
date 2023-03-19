include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "ccpmat.mm"
include "co.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "cpl1.mm"
include "cmat.mm"
include "cbs.mm"
include "cmpt2.mm"
include "df-cpmat.mm"
include "a1i.mm"
include "simpl.mm"
include "fveq2.mm"
include "adantl.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabexg.mm"
include "mp1i.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem cpmat
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vr: setvar r
  assume cpmat.s: |- S = ( N ConstPolyMat R )
  assume cpmat.p: |- P = ( Poly1 ` R )
  assume cpmat.c: |- C = ( N Mat P )
  assume cpmat.b: |- B = ( Base ` C )

  disjoint B m
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N m
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint j k
  disjoint j m
  disjoint k m
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint N n
  disjoint N r
  disjoint i n
  disjoint i r
  disjoint j n
  disjoint j r
  disjoint k n
  disjoint k r
  disjoint R n
  disjoint R r
  disjoint V n
  disjoint V r
  assert |- ( ( N e. Fin /\ R e. V ) -> S = { m e. B | A. i e. N A. j e. N A. k e. NN ( ( coe1 ` ( i m j ) ) ` k ) = ( 0g ` R ) } )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cS
    cN
    cR
    ccpmat
    co
    vk
    cv
    vi
    cv
    vj
    cv
    vm
    cv
    co
    cco1
    cfv
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    vk
    cn
    wral
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    vm
    cB
    crab
    #
    cpmat.s
    @2
    vn
    vr
    cN
    cR
    cfn
    cvv
    @3
    vr
    cv
    #
    c0g
    cfv
    #
    wceq
    #
    vk
    cn
    wral
    #
    vj
    vn
    cv
    #
    wral
    #
    vi
    @14
    wral
    #
    vm
    @14
    @10
    cpl1
    cfv
    #
    cmat
    co
    #
    cbs
    cfv
    #
    crab
    #
    @9
    ccpmat
    cvv
    ccpmat
    vn
    vr
    cfn
    cvv
    @20
    cmpt2
    wceq
    @2
    vi
    vj
    vk
    vm
    vn
    vr
    df-cpmat
    a1i
    @14
    cN
    wceq
    #
    @10
    cR
    wceq
    #
    wa
    #
    @20
    @9
    wceq
    @2
    @23
    @16
    @8
    vm
    @19
    cB
    @23
    @19
    cN
    cR
    cpl1
    cfv
    #
    cmat
    co
    #
    cbs
    cfv
    #
    cB
    @23
    @18
    @25
    cbs
    @23
    @14
    cN
    @17
    @24
    cmat
    @21
    @22
    simpl
    #
    @22
    @17
    @24
    wceq
    @21
    @10
    cR
    cpl1
    fveq2
    adantl
    oveq12d
    fveq2d
    cB
    cC
    cbs
    cfv
    #
    @26
    cpmat.b
    cC
    @25
    cbs
    cC
    cN
    cP
    cmat
    co
    @25
    cpmat.c
    cP
    @24
    cN
    cmat
    cpmat.p
    oveq2i
    eqtri
    fveq2i
    eqtri
    syl6eqr
    @23
    @15
    @7
    vi
    @14
    cN
    @27
    @23
    @13
    @6
    vj
    @14
    cN
    @27
    @23
    @12
    @5
    vk
    cn
    @23
    @11
    @4
    @3
    @22
    @11
    @4
    wceq
    @21
    @10
    cR
    c0g
    fveq2
    adantl
    eqeq2d
    ralbidv
    raleqbidv
    raleqbidv
    rabeqbidv
    adantl
    @0
    @1
    simpl
    @1
    cR
    cvv
    wcel
    @0
    cR
    cV
    elex
    adantl
    cB
    cvv
    wcel
    @9
    cvv
    wcel
    @2
    cB
    @28
    cvv
    cpmat.b
    cC
    cbs
    fvex
    eqeltri
    @8
    vm
    cB
    cvv
    rabexg
    mp1i
    ovmpt2d
    syl5eq
end
