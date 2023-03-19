include "cin.mm"
include "wbr.mm"
include "csn.mm"
include "wceq.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatlssel.mm"
include "lssincl.mm"
include "syl3anc.mm"
include "lsatcveq0.mm"
include "lcvexch.mm"
include "bitr3d.mm"

theorem lcvp
  let wph: wff ph
  let cA: class A
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cW: class W
  let c.0: class .0.
  assume lcvp.s: |- S = ( LSubSp ` W )
  assume lcvp.p: |- .(+) = ( LSSum ` W )
  assume lcvp.o: |- .0. = ( 0g ` W )
  assume lcvp.a: |- A = ( LSAtoms ` W )
  assume lcvp.c: |- C = ( <oL ` W )
  assume lcvp.w: |- ( ph -> W e. LVec )
  assume lcvp.u: |- ( ph -> U e. S )
  assume lcvp.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( ( U i^i Q ) = { .0. } <-> U C ( U .(+) Q ) ) )

  proof
    wph
    cU
    cQ
    cin
    #
    cQ
    cC
    wbr
    @0
    c.0
    csn
    wceq
    cU
    cU
    cQ
    c.po
    co
    cC
    wbr
    wph
    cA
    cC
    cQ
    cS
    @0
    cW
    c.0
    lcvp.o
    lcvp.s
    lcvp.a
    lcvp.c
    lcvp.w
    wph
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    cQ
    cS
    wcel
    @0
    cS
    wcel
    wph
    cW
    clvec
    wcel
    @1
    lcvp.w
    cW
    lveclmod
    syl
    #
    lcvp.u
    wph
    cA
    cS
    cQ
    cW
    lcvp.s
    lcvp.a
    @2
    lcvp.q
    lsatlssel
    #
    cS
    cU
    cQ
    cW
    lcvp.s
    lssincl
    syl3anc
    lcvp.q
    lsatcveq0
    wph
    cC
    c.po
    cS
    cU
    cQ
    cW
    lcvp.s
    lcvp.p
    lcvp.c
    @2
    lcvp.u
    @3
    lcvexch
    bitr3d
end
