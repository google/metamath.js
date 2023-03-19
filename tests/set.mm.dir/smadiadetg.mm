include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "w3a.mm"
include "cmarrep.mm"
include "co.mm"
include "cminmar1.mm"
include "csubma.mm"
include "eqid.mm"
include "ccrg.mm"
include "a1i.mm"
include "crg.mm"
include "crngring.mm"
include "mp1i.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "marrepcl.mm"
include "syl32anc.mm"
include "minmar1cl.mm"
include "syl22anc.mm"
include "smadiadetglem2.mm"
include "smadiadetglem1.mm"
include "mdetrsca.mm"
include "wceq.mm"
include "smadiadet.mm"
include "3adant3.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem smadiadetg
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cE: class E
  let cK: class K
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  assume smadiadet.a: |- A = ( N Mat R )
  assume smadiadet.b: |- B = ( Base ` A )
  assume smadiadet.r: |- R e. CRing
  assume smadiadet.d: |- D = ( N maDet R )
  assume smadiadet.h: |- E = ( ( N \ { K } ) maDet R )
  assume smadiadetg.x: |- .x. = ( .r ` R )


  assert |- ( ( M e. B /\ K e. N /\ S e. ( Base ` R ) ) -> ( D ` ( K ( M ( N matRRep R ) S ) K ) ) = ( S .x. ( E ` ( K ( ( N subMat R ) ` M ) K ) ) ) )

  proof
    cM
    cB
    wcel
    #
    cK
    cN
    wcel
    #
    cS
    cR
    cbs
    cfv
    #
    wcel
    #
    w3a
    #
    cK
    cK
    cM
    cS
    cN
    cR
    cmarrep
    co
    co
    co
    #
    cD
    cfv
    cS
    cK
    cK
    cM
    cN
    cR
    cminmar1
    co
    cfv
    co
    #
    cD
    cfv
    #
    c.x
    co
    cS
    cK
    cK
    cM
    cN
    cR
    csubma
    co
    cfv
    co
    cE
    cfv
    #
    c.x
    co
    @4
    cA
    cB
    cD
    cR
    c.x
    cK
    @2
    cN
    @5
    cS
    @6
    smadiadet.d
    smadiadet.a
    smadiadet.b
    @2
    eqid
    smadiadetg.x
    cR
    ccrg
    wcel
    #
    @4
    smadiadet.r
    a1i
    @4
    cR
    crg
    wcel
    #
    @0
    @3
    @1
    @1
    @5
    cB
    wcel
    @9
    @10
    @4
    smadiadet.r
    cR
    crngring
    mp1i
    #
    @0
    @1
    @3
    simp1
    #
    @0
    @1
    @3
    simp3
    #
    @0
    @1
    @3
    simp2
    #
    @14
    cA
    cB
    cR
    cS
    cK
    cK
    cM
    cN
    smadiadet.a
    smadiadet.b
    marrepcl
    syl32anc
    @13
    @4
    @10
    @0
    @1
    @1
    @6
    cB
    wcel
    @11
    @12
    @14
    @14
    cA
    cB
    cR
    cK
    cK
    cM
    cN
    smadiadet.a
    smadiadet.b
    minmar1cl
    syl22anc
    @14
    cA
    cB
    cD
    cR
    cS
    c.x
    cE
    cK
    cM
    cN
    smadiadet.a
    smadiadet.b
    smadiadet.r
    smadiadet.d
    smadiadet.h
    smadiadetg.x
    smadiadetglem2
    cA
    cB
    cD
    cR
    cS
    cE
    cK
    cM
    cN
    smadiadet.a
    smadiadet.b
    smadiadet.r
    smadiadet.d
    smadiadet.h
    smadiadetglem1
    mdetrsca
    @4
    @7
    @8
    cS
    c.x
    @4
    @8
    @7
    @0
    @1
    @8
    @7
    wceq
    @3
    cA
    cB
    cD
    cR
    cE
    cK
    cM
    cN
    smadiadet.a
    smadiadet.b
    smadiadet.r
    smadiadet.d
    smadiadet.h
    smadiadet
    3adant3
    eqcomd
    oveq2d
    eqtrd
end
