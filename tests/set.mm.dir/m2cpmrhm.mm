include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "crg.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crh.mm"
include "crngring.mm"
include "matring.mm"
include "sylan2.mm"
include "csubrg.mm"
include "cpmatsrgpmat.mm"
include "subrgring.mm"
include "syl.mm"
include "jca.mm"
include "m2cpmghm.mm"
include "m2cpmmhm.mm"
include "eqid.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem m2cpmrhm
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let vb: setvar b
  let vm: setvar m
  assume m2cpm.s: |- S = ( N ConstPolyMat R )
  assume m2cpm.t: |- T = ( N matToPolyMat R )
  assume m2cpm.a: |- A = ( N Mat R )
  assume m2cpm.b: |- B = ( Base ` A )
  assume m2cpmghm.p: |- P = ( Poly1 ` R )
  assume m2cpmghm.c: |- C = ( N Mat P )
  assume m2cpmghm.u: |- U = ( C |`s S )


  assert |- ( ( N e. Fin /\ R e. CRing ) -> T e. ( A RingHom U ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cA
    crg
    wcel
    #
    cU
    crg
    wcel
    #
    wa
    cT
    cA
    cU
    cghm
    co
    wcel
    #
    cT
    cA
    cmgp
    cfv
    #
    cU
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    wa
    cT
    cA
    cU
    crh
    co
    wcel
    @2
    @3
    @4
    @1
    @0
    cR
    crg
    wcel
    #
    @3
    cR
    crngring
    #
    cA
    cR
    cN
    m2cpm.a
    matring
    sylan2
    @2
    cS
    cC
    csubrg
    cfv
    wcel
    #
    @4
    @1
    @0
    @9
    @11
    @10
    cC
    cP
    cR
    cS
    cN
    m2cpm.s
    m2cpmghm.p
    m2cpmghm.c
    cpmatsrgpmat
    sylan2
    cS
    cC
    cU
    m2cpmghm.u
    subrgring
    syl
    jca
    @2
    @5
    @8
    @1
    @0
    @9
    @5
    @10
    cA
    cB
    cC
    cP
    cR
    cS
    cT
    cU
    cN
    m2cpm.s
    m2cpm.t
    m2cpm.a
    m2cpm.b
    m2cpmghm.p
    m2cpmghm.c
    m2cpmghm.u
    m2cpmghm
    sylan2
    cA
    cB
    cC
    cP
    cR
    cS
    cT
    cU
    cN
    m2cpm.s
    m2cpm.t
    m2cpm.a
    m2cpm.b
    m2cpmghm.p
    m2cpmghm.c
    m2cpmghm.u
    m2cpmmhm
    jca
    cA
    cU
    cT
    @6
    @7
    @6
    eqid
    @7
    eqid
    isrhm
    sylanbrc
end
