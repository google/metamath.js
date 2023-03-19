include "wceq.mm"
include "wa.mm"
include "cstrkg.mm"
include "wcel.mm"
include "adantr.mm"
include "co.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "axtgbtwnid.mm"
include "tgcgreq.mm"
include "eqtr3d.mm"
include "wne.mm"
include "wo.mm"
include "btwncolg3.mm"
include "lnid.mm"
include "pm2.61dane.mm"

theorem tgidinside
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
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
  assume lnxfr.r: |- .~ = ( cgrG ` G )
  assume lnxfr.a: |- ( ph -> A e. P )
  assume lnxfr.b: |- ( ph -> B e. P )
  assume lnxfr.d: |- .- = ( dist ` G )
  assume tgidinside.1: |- ( ph -> Z e. ( X I Y ) )
  assume tgidinside.2: |- ( ph -> ( X .- Z ) = ( X .- A ) )
  assume tgidinside.3: |- ( ph -> ( Y .- Z ) = ( Y .- A ) )


  assert |- ( ph -> Z = A )

  proof
    wph
    cZ
    cA
    wceq
    cX
    cY
    wph
    cX
    cY
    wceq
    #
    wa
    #
    cX
    cZ
    cA
    @1
    cP
    cG
    cI
    c.mi
    cX
    cZ
    tglngval.p
    lnxfr.d
    tglngval.i
    wph
    cG
    cstrkg
    wcel
    #
    @0
    tglngval.g
    adantr
    #
    wph
    cX
    cP
    wcel
    #
    @0
    tglngval.x
    adantr
    #
    wph
    cZ
    cP
    wcel
    #
    @0
    tgcolg.z
    adantr
    #
    @1
    cZ
    cX
    cY
    cI
    co
    #
    cX
    cX
    cI
    co
    wph
    cZ
    @8
    wcel
    @0
    tgidinside.1
    adantr
    @1
    cX
    cY
    cX
    cI
    wph
    @0
    simpr
    oveq2d
    eleqtrrd
    axtgbtwnid
    #
    @1
    cX
    cZ
    cX
    cA
    cP
    cG
    cI
    c.mi
    tglngval.p
    lnxfr.d
    tglngval.i
    @3
    @5
    @7
    @5
    wph
    cA
    cP
    wcel
    #
    @0
    lnxfr.a
    adantr
    wph
    cX
    cZ
    c.mi
    co
    cX
    cA
    c.mi
    co
    wceq
    #
    @0
    tgidinside.2
    adantr
    @9
    tgcgreq
    eqtr3d
    wph
    cX
    cY
    wne
    #
    wa
    cA
    cB
    cP
    c.sm
    cG
    cI
    cL
    c.mi
    cX
    cY
    cZ
    tglngval.p
    tglngval.l
    tglngval.i
    wph
    @2
    @12
    tglngval.g
    adantr
    wph
    @4
    @12
    tglngval.x
    adantr
    wph
    cY
    cP
    wcel
    @12
    tglngval.y
    adantr
    wph
    @6
    @12
    tgcolg.z
    adantr
    lnxfr.r
    wph
    @10
    @12
    lnxfr.a
    adantr
    wph
    cB
    cP
    wcel
    @12
    lnxfr.b
    adantr
    lnxfr.d
    wph
    @12
    simpr
    wph
    cY
    cX
    cZ
    cL
    co
    wcel
    cX
    cZ
    wceq
    wo
    @12
    wph
    cP
    cG
    cI
    cL
    cX
    cZ
    cY
    tglngval.p
    tglngval.l
    tglngval.i
    tglngval.g
    tglngval.x
    tgcolg.z
    tglngval.y
    tgidinside.1
    btwncolg3
    adantr
    wph
    @11
    @12
    tgidinside.2
    adantr
    wph
    cY
    cZ
    c.mi
    co
    cY
    cA
    c.mi
    co
    wceq
    @12
    tgidinside.3
    adantr
    lnid
    pm2.61dane
end
