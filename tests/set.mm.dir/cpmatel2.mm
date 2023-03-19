include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "wrex.mm"
include "cpmatel.mm"
include "wa.mm"
include "cbs.mm"
include "wb.mm"
include "simpl2.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl3.mm"
include "matecld.mm"
include "cply1coe0bi.mm"
include "syl2anc.mm"
include "bicomd.mm"
include "2ralbidva.mm"
include "bitrd.mm"

theorem cpmatel2
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
  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> ( M e. S <-> A. i e. N A. j e. N E. k e. K ( i M j ) = ( A ` k ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cM
    cS
    wcel
    vl
    cv
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
    cfv
    cR
    c0g
    cfv
    #
    wceq
    vl
    cn
    wral
    #
    vj
    cN
    wral
    vi
    cN
    wral
    @6
    vk
    cv
    cA
    cfv
    wceq
    vk
    cK
    wrex
    #
    vj
    cN
    wral
    vi
    cN
    wral
    cB
    cC
    cP
    cR
    cS
    vi
    vj
    vl
    cM
    cN
    crg
    cpmat.s
    cpmat.p
    cpmat.c
    cpmat.b
    cpmatel
    @3
    @8
    @9
    vi
    vj
    cN
    cN
    @3
    @4
    cN
    wcel
    #
    @5
    cN
    wcel
    #
    wa
    #
    wa
    #
    @9
    @8
    @13
    @1
    @6
    cP
    cbs
    cfv
    #
    wcel
    @9
    @8
    wb
    @0
    @1
    @2
    @12
    simpl2
    @13
    cC
    cB
    cP
    @4
    @5
    @14
    cM
    cN
    cpmat.c
    @14
    eqid
    #
    cpmat.b
    @3
    @10
    @11
    simprl
    @3
    @10
    @11
    simprr
    @0
    @1
    @2
    @12
    simpl3
    matecld
    cA
    @14
    cP
    cR
    vl
    cK
    @6
    @7
    vk
    cpmatel2.k
    @7
    eqid
    cpmat.p
    @15
    cpmatel2.a
    cply1coe0bi
    syl2anc
    bicomd
    2ralbidva
    bitrd
end
