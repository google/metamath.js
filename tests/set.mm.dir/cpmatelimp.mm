include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "cpmatpmat.mm"
include "3expa.mm"
include "wb.mm"
include "cpmatel.mm"
include "biimpd.mm"
include "impancom.mm"
include "jcai.mm"
include "ex.mm"

theorem cpmatelimp
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
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let cV: class V
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
  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( M e. S -> ( M e. B /\ A. i e. N A. j e. N A. k e. NN ( ( coe1 ` ( i M j ) ) ` k ) = ( 0g ` R ) ) ) )

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
    cM
    cS
    wcel
    #
    cM
    cB
    wcel
    #
    vk
    cv
    vi
    cv
    vj
    cv
    cM
    co
    cco1
    cfv
    cfv
    cR
    c0g
    cfv
    wceq
    vk
    cn
    wral
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wa
    @2
    @3
    wa
    @4
    @5
    @0
    @1
    @3
    @4
    cB
    cC
    cP
    cR
    cS
    cM
    cN
    crg
    cpmat.s
    cpmat.p
    cpmat.c
    cpmat.b
    cpmatpmat
    3expa
    @2
    @4
    @3
    @5
    @2
    @4
    wa
    @3
    @5
    @0
    @1
    @4
    @3
    @5
    wb
    cB
    cC
    cP
    cR
    cS
    vi
    vj
    vk
    cM
    cN
    crg
    cpmat.s
    cpmat.p
    cpmat.c
    cpmat.b
    cpmatel
    3expa
    biimpd
    impancom
    jcai
    ex
end
