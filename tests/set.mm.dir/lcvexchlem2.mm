include "cin.mm"
include "co.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "clmod.mm"
include "lsssssubg.mm"
include "syl.mm"
include "sseldd.mm"
include "lsmmod.mm"
include "syl31anc.mm"
include "lssincl.mm"
include "syl3anc.mm"
include "lsmss2.mm"
include "eqtr3d.mm"

theorem lcvexchlem2
  let wph: wff ph
  let cC: class C
  let c.po: class .(+)
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let vr: setvar r
  let vs: setvar s
  assume lcvexch.s: |- S = ( LSubSp ` W )
  assume lcvexch.p: |- .(+) = ( LSSum ` W )
  assume lcvexch.c: |- C = ( <oL ` W )
  assume lcvexch.w: |- ( ph -> W e. LMod )
  assume lcvexch.t: |- ( ph -> T e. S )
  assume lcvexch.u: |- ( ph -> U e. S )
  assume lcvexch.r: |- ( ph -> R e. S )
  assume lcvexch.a: |- ( ph -> ( T i^i U ) C_ R )
  assume lcvexch.b: |- ( ph -> R C_ U )


  assert |- ( ph -> ( ( R .(+) T ) i^i U ) = R )

  proof
    wph
    cR
    cT
    cU
    cin
    #
    c.po
    co
    #
    cR
    cT
    c.po
    co
    cU
    cin
    #
    cR
    wph
    cR
    cW
    csubg
    cfv
    #
    wcel
    #
    cT
    @3
    wcel
    cU
    @3
    wcel
    cR
    cU
    wss
    @1
    @2
    wceq
    wph
    cS
    @3
    cR
    wph
    cW
    clmod
    wcel
    #
    cS
    @3
    wss
    lcvexch.w
    cS
    cW
    lcvexch.s
    lsssssubg
    syl
    #
    lcvexch.r
    sseldd
    #
    wph
    cS
    @3
    cT
    @6
    lcvexch.t
    sseldd
    wph
    cS
    @3
    cU
    @6
    lcvexch.u
    sseldd
    lcvexch.b
    c.po
    cR
    cT
    cU
    cW
    lcvexch.p
    lsmmod
    syl31anc
    wph
    @4
    @0
    @3
    wcel
    @0
    cR
    wss
    @1
    cR
    wceq
    @7
    wph
    cS
    @3
    @0
    @6
    wph
    @5
    cT
    cS
    wcel
    cU
    cS
    wcel
    @0
    cS
    wcel
    lcvexch.w
    lcvexch.t
    lcvexch.u
    cS
    cT
    cU
    cW
    lcvexch.s
    lssincl
    syl3anc
    sseldd
    lcvexch.a
    c.po
    cR
    @0
    cW
    lcvexch.p
    lsmss2
    syl3anc
    eqtr3d
end
