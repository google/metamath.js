include "cfn.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cdmatalt.mm"
include "co.mm"
include "cv.mm"
include "wne.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cress.mm"
include "cmat.mm"
include "c0g.mm"
include "cfv.mm"
include "cbs.mm"
include "csb.mm"
include "ovexd.mm"
include "id.mm"
include "fveq2.mm"
include "rabeq.mm"
include "syl.mm"
include "oveq12d.mm"
include "adantl.mm"
include "csbied.mm"
include "oveq12.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "simpl.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "eqtrd.mm"
include "df-dmatalt.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "syl5eq.mm"

theorem dmatALTval
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let cN: class N
  let c.0: class .0.
  let vn: setvar n
  let vr: setvar r
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume dmatALTval.a: |- A = ( N Mat R )
  assume dmatALTval.b: |- B = ( Base ` A )
  assume dmatALTval.0: |- .0. = ( 0g ` R )
  assume dmatALTval.d: |- D = ( N DMatALT R )

  disjoint B m
  disjoint N i
  disjoint N j
  disjoint N m
  disjoint i j
  disjoint i m
  disjoint j m
  disjoint R i
  disjoint R j
  disjoint R m
  disjoint A n
  disjoint A r
  disjoint n r
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint N a
  disjoint N n
  disjoint N r
  disjoint a i
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint i n
  disjoint i r
  disjoint j n
  disjoint j r
  disjoint R a
  disjoint R n
  disjoint R r
  disjoint .0. n
  disjoint .0. r
  disjoint k x
  assert |- ( ( N e. Fin /\ R e. _V ) -> D = ( A |`s { m e. B | A. i e. N A. j e. N ( i =/= j -> ( i m j ) = .0. ) } ) )

  proof
    cN
    cfn
    wcel
    cR
    cvv
    wcel
    wa
    cD
    cN
    cR
    cdmatalt
    co
    cA
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @0
    @1
    vm
    cv
    co
    #
    c.0
    wceq
    #
    wi
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
    cress
    co
    #
    dmatALTval.d
    vn
    vr
    cN
    cR
    cfn
    cvv
    va
    vn
    cv
    #
    vr
    cv
    #
    cmat
    co
    #
    va
    cv
    #
    @2
    @3
    @11
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vj
    @10
    wral
    #
    vi
    @10
    wral
    #
    vm
    @13
    cbs
    cfv
    #
    crab
    #
    cress
    co
    #
    csb
    #
    @9
    cdmatalt
    @10
    cN
    wceq
    #
    @11
    cR
    wceq
    #
    wa
    #
    @22
    @12
    @18
    vm
    @12
    cbs
    cfv
    #
    crab
    #
    cress
    co
    #
    @9
    @25
    va
    @12
    @21
    @28
    cvv
    @25
    @10
    @11
    cmat
    ovexd
    @13
    @12
    wceq
    #
    @21
    @28
    wceq
    @25
    @29
    @13
    @12
    @20
    @27
    cress
    @29
    id
    @29
    @19
    @26
    wceq
    @20
    @27
    wceq
    @13
    @12
    cbs
    fveq2
    @18
    vm
    @19
    @26
    rabeq
    syl
    oveq12d
    adantl
    csbied
    @25
    @12
    cA
    @27
    @8
    cress
    @25
    @12
    cN
    cR
    cmat
    co
    cA
    @10
    cN
    @11
    cR
    cmat
    oveq12
    dmatALTval.a
    syl6eqr
    #
    @25
    @18
    @7
    vm
    @26
    cB
    @25
    @26
    cA
    cbs
    cfv
    cB
    @25
    @12
    cA
    cbs
    @30
    fveq2d
    dmatALTval.b
    syl6eqr
    @25
    @17
    @6
    vi
    @10
    cN
    @23
    @24
    simpl
    #
    @25
    @16
    @5
    vj
    @10
    cN
    @31
    @25
    @15
    @4
    @2
    @25
    @14
    c.0
    @3
    @24
    @14
    c.0
    wceq
    @23
    @24
    @14
    cR
    c0g
    cfv
    c.0
    @11
    cR
    c0g
    fveq2
    dmatALTval.0
    syl6eqr
    adantl
    eqeq2d
    imbi2d
    raleqbidv
    raleqbidv
    rabeqbidv
    oveq12d
    eqtrd
    vi
    vj
    vm
    vn
    vr
    va
    df-dmatalt
    cA
    @8
    cress
    ovex
    ovmpt2a
    syl5eq
end
