include "cin.mm"
include "wbr.mm"
include "co.mm"
include "wa.mm"
include "clmod.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "lcvexchlem5.mm"
include "lcvexchlem4.mm"
include "impbida.mm"

theorem lcvexch
  let wph: wff ph
  let cC: class C
  let c.po: class .(+)
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


  assert |- ( ph -> ( ( T i^i U ) C U <-> T C ( T .(+) U ) ) )

  proof
    wph
    cT
    cU
    cin
    cU
    cC
    wbr
    #
    cT
    cT
    cU
    c.po
    co
    cC
    wbr
    #
    wph
    @0
    wa
    cC
    c.po
    cS
    cT
    cU
    cW
    lcvexch.s
    lcvexch.p
    lcvexch.c
    wph
    cW
    clmod
    wcel
    #
    @0
    lcvexch.w
    adantr
    wph
    cT
    cS
    wcel
    #
    @0
    lcvexch.t
    adantr
    wph
    cU
    cS
    wcel
    #
    @0
    lcvexch.u
    adantr
    wph
    @0
    simpr
    lcvexchlem5
    wph
    @1
    wa
    cC
    c.po
    cS
    cT
    cU
    cW
    lcvexch.s
    lcvexch.p
    lcvexch.c
    wph
    @2
    @1
    lcvexch.w
    adantr
    wph
    @3
    @1
    lcvexch.t
    adantr
    wph
    @4
    @1
    lcvexch.u
    adantr
    wph
    @1
    simpr
    lcvexchlem4
    impbida
end
