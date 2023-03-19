include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "cpmatpmat.mm"
include "3expa.mm"
include "wb.mm"
include "cpmatel2.mm"
include "biimpd.mm"
include "impancom.mm"
include "jcai.mm"
include "ex.mm"

theorem cpmatelimp2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let cV: class V
  let vl: setvar l
  assume cpmat.s: |- S = ( N ConstPolyMat R )
  assume cpmat.p: |- P = ( Poly1 ` R )
  assume cpmat.c: |- C = ( N Mat P )
  assume cpmat.b: |- B = ( Base ` C )
  assume cpmatel2.k: |- K = ( Base ` R )
  assume cpmatel2.a: |- A = ( algSc ` P )

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
  disjoint A k
  disjoint B i
  disjoint B j
  disjoint K k
  disjoint P k
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
  disjoint A l
  disjoint k l
  disjoint K l
  disjoint M l
  disjoint N l
  disjoint i l
  disjoint j l
  disjoint P l
  disjoint R l
  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( M e. S -> ( M e. B /\ A. i e. N A. j e. N E. k e. K ( i M j ) = ( A ` k ) ) ) )

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
    vi
    cv
    vj
    cv
    cM
    co
    vk
    cv
    cA
    cfv
    wceq
    vk
    cK
    wrex
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
    cA
    cB
    cC
    cP
    cR
    cS
    vi
    vj
    vk
    cK
    cM
    cN
    cpmat.s
    cpmat.p
    cpmat.c
    cpmat.b
    cpmatel2.k
    cpmatel2.a
    cpmatel2
    3expa
    biimpd
    impancom
    jcai
    ex
end
