include "wss.mm"
include "wn.mm"
include "co.mm"
include "wpss.mm"
include "wbr.mm"
include "csubg.mm"
include "cfv.mm"
include "clmod.mm"
include "wcel.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lsatlssel.mm"
include "lssnle.mm"
include "lcv1.mm"
include "bitr3d.mm"

theorem lcv2
  let wph: wff ph
  let cA: class A
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cW: class W
  assume lcv2.s: |- S = ( LSubSp ` W )
  assume lcv2.p: |- .(+) = ( LSSum ` W )
  assume lcv2.a: |- A = ( LSAtoms ` W )
  assume lcv2.c: |- C = ( <oL ` W )
  assume lcv2.w: |- ( ph -> W e. LVec )
  assume lcv2.u: |- ( ph -> U e. S )
  assume lcv2.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( U C. ( U .(+) Q ) <-> U C ( U .(+) Q ) ) )

  proof
    wph
    cQ
    cU
    wss
    wn
    cU
    cU
    cQ
    c.po
    co
    #
    wpss
    cU
    @0
    cC
    wbr
    wph
    c.po
    cU
    cQ
    cW
    lcv2.p
    wph
    cS
    cW
    csubg
    cfv
    #
    cU
    wph
    cW
    clmod
    wcel
    #
    cS
    @1
    wss
    wph
    cW
    clvec
    wcel
    @2
    lcv2.w
    cW
    lveclmod
    syl
    #
    cS
    cW
    lcv2.s
    lsssssubg
    syl
    #
    lcv2.u
    sseldd
    wph
    cS
    @1
    cQ
    @4
    wph
    cA
    cS
    cQ
    cW
    lcv2.s
    lcv2.a
    @3
    lcv2.q
    lsatlssel
    sseldd
    lssnle
    wph
    cA
    cC
    c.po
    cQ
    cS
    cU
    cW
    lcv2.s
    lcv2.p
    lcv2.a
    lcv2.c
    lcv2.w
    lcv2.u
    lcv2.q
    lcv1
    bitr3d
end
