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
include "cfzo.mm"
include "fzossnn.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "elfzle1.mm"
include "nnred.mm"
include "lenltd.mm"
include "mpbid.mm"
include "iffalsed.mm"
include "elfzolt2.mm"
include "iftrued.mm"
include "smatlem.mm"

theorem smattr
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
  assume smattr.i: |- ( ph -> I e. ( K ... M ) )
  assume smattr.j: |- ( ph -> J e. ( 1 ..^ L ) )


  assert |- ( ph -> ( I S J ) = ( ( I + 1 ) A J ) )

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
    @1
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
    smattr.i
    sseldd
    #
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
    smattr.j
    sseldi
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
    @5
    wn
    wph
    cI
    @1
    wcel
    @6
    smattr.i
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
    @2
    nnred
    wph
    cI
    @3
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
    cJ
    c1
    caddc
    co
    wph
    cJ
    @4
    wcel
    @7
    smattr.j
    cJ
    c1
    cL
    elfzolt2
    syl
    iftrued
    smatlem
end
