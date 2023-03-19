include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "w3a.mm"
include "crab.mm"
include "wa.mm"
include "cpmat.mm"
include "3adant3.mm"
include "eleq2d.mm"
include "oveq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "3anibar.mm"

theorem cpmatel
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assume cpmat.s: |- S = ( N ConstPolyMat R )
  assume cpmat.p: |- P = ( Poly1 ` R )
  assume cpmat.c: |- C = ( N Mat P )
  assume cpmat.b: |- B = ( Base ` C )

  disjoint N i
  disjoint N j
  disjoint N k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint V n
  disjoint V r
  disjoint M m
  assert |- ( ( N e. Fin /\ R e. V /\ M e. B ) -> ( M e. S <-> A. i e. N A. j e. N A. k e. NN ( ( coe1 ` ( i M j ) ) ` k ) = ( 0g ` R ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    cM
    cB
    wcel
    #
    cM
    cS
    wcel
    #
    vk
    cv
    #
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cco1
    cfv
    #
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
    vi
    cN
    wral
    #
    @0
    @1
    @2
    w3a
    #
    @3
    cM
    @4
    @5
    @6
    vm
    cv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @10
    wceq
    #
    vk
    cn
    wral
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    vm
    cB
    crab
    #
    wcel
    @2
    @13
    wa
    @14
    cS
    @22
    cM
    @0
    @1
    cS
    @22
    wceq
    @2
    cB
    cC
    cP
    cR
    cS
    vi
    vj
    vk
    vm
    cN
    cV
    cpmat.s
    cpmat.p
    cpmat.c
    cpmat.b
    cpmat
    3adant3
    eleq2d
    @21
    @13
    vm
    cM
    cB
    @15
    cM
    wceq
    #
    @20
    @12
    vi
    vj
    cN
    cN
    @23
    @19
    @11
    vk
    cn
    @23
    @18
    @9
    @10
    @23
    @4
    @17
    @8
    @23
    @16
    @7
    cco1
    @5
    @6
    @15
    cM
    oveq
    fveq2d
    fveq1d
    eqeq1d
    ralbidv
    2ralbidv
    elrab
    syl6bb
    3anibar
end
