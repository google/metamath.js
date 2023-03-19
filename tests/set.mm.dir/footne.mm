include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "cstrkg.mm"
include "adantr.mm"
include "crn.mm"
include "perpln1.mm"
include "wne.mm"
include "perpneq.mm"
include "necomd.mm"
include "tglnpt.mm"
include "tglnne.mm"
include "tglinerflx1.mm"
include "elind.mm"
include "simpr.mm"
include "tglinerflx2.mm"
include "tglineineq.mm"
include "pm2.21ddne.mm"
include "pm2.01da.mm"

theorem footne
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let cB: class B
  let vg: setvar g
  assume isperp.p: |- P = ( Base ` G )
  assume isperp.d: |- .- = ( dist ` G )
  assume isperp.i: |- I = ( Itv ` G )
  assume isperp.l: |- L = ( LineG ` G )
  assume isperp.g: |- ( ph -> G e. TarskiG )
  assume isperp.a: |- ( ph -> A e. ran L )
  assume footne.x: |- ( ph -> X e. A )
  assume footne.y: |- ( ph -> Y e. P )
  assume footne.1: |- ( ph -> ( X L Y ) ( perpG ` G ) A )


  assert |- ( ph -> -. Y e. A )

  proof
    wph
    cY
    cA
    wcel
    #
    wph
    @0
    wa
    #
    @0
    wn
    cX
    cY
    @1
    cA
    cX
    cY
    cL
    co
    #
    cP
    cG
    cI
    cL
    cX
    cY
    isperp.p
    isperp.i
    isperp.l
    wph
    cG
    cstrkg
    wcel
    @0
    isperp.g
    adantr
    wph
    cA
    cL
    crn
    #
    wcel
    @0
    isperp.a
    adantr
    wph
    @2
    @3
    wcel
    @0
    wph
    @2
    cA
    cG
    cL
    isperp.l
    isperp.g
    footne.1
    perpln1
    #
    adantr
    wph
    cA
    @2
    wne
    @0
    wph
    @2
    cA
    wph
    @2
    cA
    cP
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    isperp.g
    @4
    isperp.a
    footne.1
    perpneq
    necomd
    adantr
    @1
    cA
    @2
    cX
    wph
    cX
    cA
    wcel
    @0
    footne.x
    adantr
    wph
    cX
    @2
    wcel
    @0
    wph
    cP
    cX
    cY
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    isperp.g
    wph
    cA
    cP
    cG
    cI
    cL
    cX
    isperp.p
    isperp.l
    isperp.i
    isperp.g
    isperp.a
    footne.x
    tglnpt
    #
    footne.y
    wph
    cP
    cG
    cI
    cL
    cX
    cY
    isperp.p
    isperp.i
    isperp.l
    isperp.g
    @5
    footne.y
    @4
    tglnne
    #
    tglinerflx1
    adantr
    elind
    @1
    cA
    @2
    cY
    wph
    @0
    simpr
    wph
    cY
    @2
    wcel
    @0
    wph
    cP
    cX
    cY
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    isperp.g
    @5
    footne.y
    @6
    tglinerflx2
    adantr
    elind
    tglineineq
    wph
    cX
    cY
    wne
    @0
    @6
    adantr
    pm2.21ddne
    pm2.01da
end
