include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "btwncolg1.mm"
include "btwncolg2.mm"
include "btwncolg3.mm"
include "tgdim01.mm"
include "mpjao3dan.mm"

theorem tgdim01ln
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tglngval.p: |- P = ( Base ` G )
  assume tglngval.l: |- L = ( LineG ` G )
  assume tglngval.i: |- I = ( Itv ` G )
  assume tglngval.g: |- ( ph -> G e. TarskiG )
  assume tglngval.x: |- ( ph -> X e. P )
  assume tglngval.y: |- ( ph -> Y e. P )
  assume tgcolg.z: |- ( ph -> Z e. P )
  assume tgdim01ln.1: |- ( ph -> -. G TarskiGDim>= 2 )


  assert |- ( ph -> ( Z e. ( X L Y ) \/ X = Y ) )

  proof
    wph
    cZ
    cX
    cY
    cI
    co
    wcel
    #
    cZ
    cX
    cY
    cL
    co
    wcel
    cX
    cY
    wceq
    wo
    cX
    cZ
    cY
    cI
    co
    wcel
    #
    cY
    cX
    cZ
    cI
    co
    wcel
    #
    wph
    @0
    wa
    cP
    cG
    cI
    cL
    cX
    cY
    cZ
    tglngval.p
    tglngval.l
    tglngval.i
    wph
    cG
    cstrkg
    wcel
    #
    @0
    tglngval.g
    adantr
    wph
    cX
    cP
    wcel
    #
    @0
    tglngval.x
    adantr
    wph
    cY
    cP
    wcel
    #
    @0
    tglngval.y
    adantr
    wph
    cZ
    cP
    wcel
    #
    @0
    tgcolg.z
    adantr
    wph
    @0
    simpr
    btwncolg1
    wph
    @1
    wa
    cP
    cG
    cI
    cL
    cX
    cY
    cZ
    tglngval.p
    tglngval.l
    tglngval.i
    wph
    @3
    @1
    tglngval.g
    adantr
    wph
    @4
    @1
    tglngval.x
    adantr
    wph
    @5
    @1
    tglngval.y
    adantr
    wph
    @6
    @1
    tgcolg.z
    adantr
    wph
    @1
    simpr
    btwncolg2
    wph
    @2
    wa
    cP
    cG
    cI
    cL
    cX
    cY
    cZ
    tglngval.p
    tglngval.l
    tglngval.i
    wph
    @3
    @2
    tglngval.g
    adantr
    wph
    @4
    @2
    tglngval.x
    adantr
    wph
    @5
    @2
    tglngval.y
    adantr
    wph
    @6
    @2
    tgcolg.z
    adantr
    wph
    @2
    simpr
    btwncolg3
    wph
    cP
    cG
    cI
    cstrkg
    cX
    cY
    cZ
    tglngval.p
    tglngval.i
    tglngval.g
    tgdim01ln.1
    tglngval.x
    tglngval.y
    tgcolg.z
    tgdim01
    mpjao3dan
end
