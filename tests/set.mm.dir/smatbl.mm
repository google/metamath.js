include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "cn.mm"
include "fzossnn.mm"
include "sseldi.mm"
include "cfz.mm"
include "wcel.mm"
include "wss.mm"
include "fz1ssnn.mm"
include "fzssnn.mm"
include "syl.mm"
include "sseldd.mm"
include "clt.mm"
include "wbr.mm"
include "elfzolt2.mm"
include "iftrued.mm"
include "cle.mm"
include "wn.mm"
include "elfzle1.mm"
include "nnred.mm"
include "lenltd.mm"
include "mpbid.mm"
include "iffalsed.mm"
include "smatlem.mm"

theorem smatbl
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
  assume smatbl.i: |- ( ph -> I e. ( 1 ..^ K ) )
  assume smatbl.j: |- ( ph -> J e. ( L ... N ) )


  assert |- ( ph -> ( I S J ) = ( I A ( J + 1 ) ) )

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
    c1
    caddc
    co
    #
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
    smatbl.i
    sseldi
    wph
    cL
    cN
    cfz
    co
    #
    cn
    cJ
    wph
    cL
    cn
    wcel
    @2
    cn
    wss
    wph
    c1
    cN
    cfz
    co
    cn
    cL
    cN
    fz1ssnn
    smat.l
    sseldi
    #
    cL
    cN
    fzssnn
    syl
    smatbl.j
    sseldd
    #
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
    @1
    wcel
    @5
    smatbl.i
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
    @0
    wph
    cL
    cJ
    cle
    wbr
    #
    @6
    wn
    wph
    cJ
    @2
    wcel
    @7
    smatbl.j
    cJ
    cL
    cN
    elfzle1
    syl
    wph
    cL
    cJ
    wph
    cL
    @3
    nnred
    wph
    cJ
    @4
    nnred
    lenltd
    mpbid
    iffalsed
    smatlem
end
