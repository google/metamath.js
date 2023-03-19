include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "co.mm"
include "cbs.mm"
include "eqid.mm"
include "mat2pmatmhm.mm"
include "csubmnd.mm"
include "crn.mm"
include "wss.mm"
include "wb.mm"
include "crg.mm"
include "csubrg.mm"
include "crngring.mm"
include "anim2i.mm"
include "cpmatsrgpmat.mm"
include "subrgsubm.mm"
include "3syl.mm"
include "wf.mm"
include "m2cpmf.mm"
include "frn.mm"
include "cress.mm"
include "cvv.mm"
include "wceq.mm"
include "cmat.mm"
include "ovex.mm"
include "eqeltri.mm"
include "ccpmat.mm"
include "mgpress.mm"
include "mp2an.mm"
include "eqcomi.mm"
include "resmhm2b.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem m2cpmmhm
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


  assert |- ( ( N e. Fin /\ R e. CRing ) -> T e. ( ( mulGrp ` A ) MndHom ( mulGrp ` U ) ) )

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
    cT
    cA
    cmgp
    cfv
    #
    cC
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    cT
    @3
    cU
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    cA
    cB
    cC
    cP
    cR
    cT
    cC
    cbs
    cfv
    #
    cN
    m2cpm.t
    m2cpm.a
    m2cpm.b
    m2cpmghm.p
    m2cpmghm.c
    @8
    eqid
    mat2pmatmhm
    @2
    cS
    @4
    csubmnd
    cfv
    wcel
    #
    cT
    crn
    cS
    wss
    #
    @5
    @7
    wb
    @2
    @0
    cR
    crg
    wcel
    #
    wa
    #
    cS
    cC
    csubrg
    cfv
    wcel
    @9
    @1
    @11
    @0
    cR
    crngring
    anim2i
    #
    cC
    cP
    cR
    cS
    cN
    m2cpm.s
    m2cpmghm.p
    m2cpmghm.c
    cpmatsrgpmat
    cS
    cC
    @4
    @4
    eqid
    #
    subrgsubm
    3syl
    @2
    @12
    cB
    cS
    cT
    wf
    @10
    @13
    cA
    cB
    cR
    cS
    cT
    cN
    m2cpm.s
    m2cpm.t
    m2cpm.a
    m2cpm.b
    m2cpmf
    cB
    cS
    cT
    frn
    3syl
    @3
    @4
    @6
    cT
    cS
    @4
    cS
    cress
    co
    #
    @6
    cC
    cvv
    wcel
    cS
    cvv
    wcel
    @15
    @6
    wceq
    cC
    cN
    cP
    cmat
    co
    cvv
    m2cpmghm.c
    cN
    cP
    cmat
    ovex
    eqeltri
    cS
    cN
    cR
    ccpmat
    co
    cvv
    m2cpm.s
    cN
    cR
    ccpmat
    ovex
    eqeltri
    cS
    cC
    cU
    @4
    cvv
    cvv
    m2cpmghm.u
    @14
    mgpress
    mp2an
    eqcomi
    resmhm2b
    syl2anc
    mpbid
end
