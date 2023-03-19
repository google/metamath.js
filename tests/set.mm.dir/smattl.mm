include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cn.mm"
include "fzossnn.mm"
include "sseldi.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "wcel.mm"
include "elfzolt2.mm"
include "syl.mm"
include "iftrued.mm"
include "smatlem.mm"

theorem smattl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let cV: class V
  let vx: setvar x
  assume smat.s: |- S = ( K ( subMat1 ` A ) L )
  assume smat.m: |- ( ph -> M e. NN )
  assume smat.n: |- ( ph -> N e. NN )
  assume smat.k: |- ( ph -> K e. ( 1 ... M ) )
  assume smat.l: |- ( ph -> L e. ( 1 ... N ) )
  assume smat.a: |- ( ph -> A e. ( B ^m ( ( 1 ... M ) X. ( 1 ... N ) ) ) )
  assume smattl.i: |- ( ph -> I e. ( 1 ..^ K ) )
  assume smattl.j: |- ( ph -> J e. ( 1 ..^ L ) )


  assert |- ( ph -> ( I S J ) = ( I A J ) )

  proof
    wph
    cA
    cB
    cS
    cI
    cJ
    cK
    cL
    cM
    cN
    cI
    cJ
    smat.s
    smat.m
    smat.n
    smat.k
    smat.l
    smat.a
    wph
    c1
    cK
    cfzo
    co
    #
    cn
    cI
    cK
    fzossnn
    smattl.i
    sseldi
    wph
    c1
    cL
    cfzo
    co
    #
    cn
    cJ
    cL
    fzossnn
    smattl.j
    sseldi
    wph
    cI
    cK
    clt
    wbr
    #
    cI
    cI
    c1
    caddc
    co
    wph
    cI
    @0
    wcel
    @2
    smattl.i
    cI
    c1
    cK
    elfzolt2
    syl
    iftrued
    wph
    cJ
    cL
    clt
    wbr
    #
    cJ
    cJ
    c1
    caddc
    co
    wph
    cJ
    @1
    wcel
    @3
    smattl.j
    cJ
    c1
    cL
    elfzolt2
    syl
    iftrued
    smatlem
end
