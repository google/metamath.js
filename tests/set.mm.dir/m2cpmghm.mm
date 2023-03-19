include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "mat2pmatghm.mm"
include "csubg.mm"
include "crn.mm"
include "wss.mm"
include "wb.mm"
include "cpmatsubgpmat.mm"
include "wf.mm"
include "m2cpmf.mm"
include "frn.mm"
include "syl.mm"
include "resghm2b.mm"
include "bicomd.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem m2cpmghm
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


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T e. ( A GrpHom U ) )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    cT
    cA
    cU
    cghm
    co
    wcel
    #
    cT
    cA
    cC
    cghm
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
    @3
    eqid
    mat2pmatghm
    @0
    cS
    cC
    csubg
    cfv
    wcel
    #
    cT
    crn
    cS
    wss
    #
    @1
    @2
    wb
    cC
    cP
    cR
    cS
    cN
    m2cpm.s
    m2cpmghm.p
    m2cpmghm.c
    cpmatsubgpmat
    @0
    cB
    cS
    cT
    wf
    @5
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
    syl
    @4
    @5
    wa
    @2
    @1
    cA
    cC
    cU
    cT
    cS
    m2cpmghm.u
    resghm2b
    bicomd
    syl2anc
    mpbird
end
