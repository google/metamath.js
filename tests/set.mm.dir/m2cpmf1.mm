include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cpl1.mm"
include "cfv.mm"
include "cmat.mm"
include "co.mm"
include "cbs.mm"
include "wf1.mm"
include "crn.mm"
include "wss.mm"
include "eqid.mm"
include "mat2pmatf1.mm"
include "wf.mm"
include "m2cpmf.mm"
include "frn.mm"
include "syl.mm"
include "f1ssr.mm"
include "syl2anc.mm"

theorem m2cpmf1
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
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


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T : B -1-1-> S )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    cB
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
    cT
    wf1
    cT
    crn
    cS
    wss
    #
    cB
    cS
    cT
    wf1
    cA
    cB
    @2
    @1
    cR
    cT
    @3
    cN
    m2cpm.t
    m2cpm.a
    m2cpm.b
    @1
    eqid
    @2
    eqid
    @3
    eqid
    mat2pmatf1
    @0
    cB
    cS
    cT
    wf
    @4
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
    cB
    @3
    cS
    cT
    f1ssr
    syl2anc
end
