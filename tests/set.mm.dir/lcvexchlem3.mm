include "co.mm"
include "cin.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "clmod.mm"
include "lsssssubg.mm"
include "syl.mm"
include "sseldd.mm"
include "lsmmod2.mm"
include "syl31anc.mm"
include "cabl.mm"
include "lmodabl.mm"
include "lsmcom.mm"
include "syl3anc.mm"
include "sseqtrd.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqtr3d.mm"

theorem lcvexchlem3
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
  assume lcvexch.q: |- ( ph -> R e. S )
  assume lcvexch.d: |- ( ph -> T C_ R )
  assume lcvexch.e: |- ( ph -> R C_ ( T .(+) U ) )


  assert |- ( ph -> ( ( R i^i U ) .(+) T ) = R )

  proof
    wph
    cR
    cU
    cT
    c.po
    co
    #
    cin
    #
    cR
    cU
    cin
    cT
    c.po
    co
    #
    cR
    wph
    cR
    cW
    csubg
    cfv
    #
    wcel
    cU
    @3
    wcel
    #
    cT
    @3
    wcel
    #
    cT
    cR
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
    lcvexch.q
    sseldd
    wph
    cS
    @3
    cU
    @7
    lcvexch.u
    sseldd
    #
    wph
    cS
    @3
    cT
    @7
    lcvexch.t
    sseldd
    #
    lcvexch.d
    c.po
    cR
    cU
    cT
    cW
    lcvexch.p
    lsmmod2
    syl31anc
    wph
    cR
    @0
    wss
    @1
    cR
    wceq
    wph
    cR
    cT
    cU
    c.po
    co
    #
    @0
    lcvexch.e
    wph
    cW
    cabl
    wcel
    #
    @5
    @4
    @10
    @0
    wceq
    wph
    @6
    @11
    lcvexch.w
    cW
    lmodabl
    syl
    @9
    @8
    c.po
    cT
    cU
    cW
    lcvexch.p
    lsmcom
    syl3anc
    sseqtrd
    cR
    @0
    df-ss
    sylib
    eqtr3d
end
