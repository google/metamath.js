include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cn.mm"
include "wcel.mm"
include "wss.mm"
include "fz1ssnn.mm"
include "sseldi.mm"
include "fzssnn.mm"
include "syl.mm"
include "sseldd.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "elfzle1.mm"
include "nnred.mm"
include "lenltd.mm"
include "mpbid.mm"
include "iffalsed.mm"
include "smatlem.mm"

theorem smatbr
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
  assume smatbr.i: |- ( ph -> I e. ( K ... M ) )
  assume smatbr.j: |- ( ph -> J e. ( L ... N ) )


  assert |- ( ph -> ( I S J ) = ( ( I + 1 ) A ( J + 1 ) ) )

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
    c1
    caddc
    co
    #
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
    cK
    cM
    cfz
    co
    #
    cn
    cI
    wph
    cK
    cn
    wcel
    @2
    cn
    wss
    wph
    c1
    cM
    cfz
    co
    cn
    cK
    cM
    fz1ssnn
    smat.k
    sseldi
    #
    cK
    cM
    fzssnn
    syl
    smatbr.i
    sseldd
    #
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
    @5
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
    smatbr.j
    sseldd
    #
    wph
    cI
    cK
    clt
    wbr
    #
    cI
    @0
    wph
    cK
    cI
    cle
    wbr
    #
    @8
    wn
    wph
    cI
    @2
    wcel
    @9
    smatbr.i
    cI
    cK
    cM
    elfzle1
    syl
    wph
    cK
    cI
    wph
    cK
    @3
    nnred
    wph
    cI
    @4
    nnred
    lenltd
    mpbid
    iffalsed
    wph
    cJ
    cL
    clt
    wbr
    #
    cJ
    @1
    wph
    cL
    cJ
    cle
    wbr
    #
    @10
    wn
    wph
    cJ
    @5
    wcel
    @11
    smatbr.j
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
    @6
    nnred
    wph
    cJ
    @7
    nnred
    lenltd
    mpbid
    iffalsed
    smatlem
end
