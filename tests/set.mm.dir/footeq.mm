include "cv.mm"
include "co.mm"
include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "footne.mm"
include "foot.mm"
include "tglnpt.mm"
include "perpln1.mm"
include "tglnne.mm"
include "tglinecom.mm"
include "eqbrtrrd.mm"
include "reu2eqd.mm"

theorem footeq
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  let vg: setvar g
  assume isperp.p: |- P = ( Base ` G )
  assume isperp.d: |- .- = ( dist ` G )
  assume isperp.i: |- I = ( Itv ` G )
  assume isperp.l: |- L = ( LineG ` G )
  assume isperp.g: |- ( ph -> G e. TarskiG )
  assume isperp.a: |- ( ph -> A e. ran L )
  assume footeq.x: |- ( ph -> X e. A )
  assume footeq.y: |- ( ph -> Y e. A )
  assume footeq.z: |- ( ph -> Z e. P )
  assume footeq.1: |- ( ph -> ( X L Z ) ( perpG ` G ) A )
  assume footeq.2: |- ( ph -> ( Y L Z ) ( perpG ` G ) A )


  assert |- ( ph -> X = Y )

  proof
    wph
    cZ
    vx
    cv
    #
    cL
    co
    #
    cA
    cG
    cperpg
    cfv
    #
    wbr
    cZ
    cX
    cL
    co
    #
    cA
    @2
    wbr
    cZ
    cY
    cL
    co
    #
    cA
    @2
    wbr
    vx
    cA
    cX
    cY
    @0
    cX
    wceq
    @1
    @3
    cA
    @2
    @0
    cX
    cZ
    cL
    oveq2
    breq1d
    @0
    cY
    wceq
    @1
    @4
    cA
    @2
    @0
    cY
    cZ
    cL
    oveq2
    breq1d
    wph
    vx
    cA
    cZ
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
    isperp.a
    footeq.z
    wph
    cA
    cP
    cG
    cI
    cL
    c.mi
    cX
    cZ
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    isperp.g
    isperp.a
    footeq.x
    footeq.z
    footeq.1
    footne
    foot
    footeq.x
    footeq.y
    wph
    cX
    cZ
    cL
    co
    #
    @3
    cA
    @2
    wph
    cP
    cX
    cZ
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
    footeq.x
    tglnpt
    #
    footeq.z
    wph
    cP
    cG
    cI
    cL
    cX
    cZ
    isperp.p
    isperp.i
    isperp.l
    isperp.g
    @6
    footeq.z
    wph
    @5
    cA
    cG
    cL
    isperp.l
    isperp.g
    footeq.1
    perpln1
    tglnne
    tglinecom
    footeq.1
    eqbrtrrd
    wph
    cY
    cZ
    cL
    co
    #
    @4
    cA
    @2
    wph
    cP
    cY
    cZ
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
    cY
    isperp.p
    isperp.l
    isperp.i
    isperp.g
    isperp.a
    footeq.y
    tglnpt
    #
    footeq.z
    wph
    cP
    cG
    cI
    cL
    cY
    cZ
    isperp.p
    isperp.i
    isperp.l
    isperp.g
    @8
    footeq.z
    wph
    @7
    cA
    cG
    cL
    isperp.l
    isperp.g
    footeq.2
    perpln1
    tglnne
    tglinecom
    footeq.2
    eqbrtrrd
    reu2eqd
end
