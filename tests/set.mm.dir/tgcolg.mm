include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "w3o.mm"
include "wb.mm"
include "wa.mm"
include "simpr.mm"
include "olcd.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "cstrkg.mm"
include "adantr.mm"
include "tgbtwntriv2.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "3mix2d.mm"
include "2thd.mm"
include "wne.mm"
include "wn.mm"
include "neneqd.mm"
include "biorf.mm"
include "syl.mm"
include "orcom.mm"
include "syl6bb.mm"
include "tgellng.mm"
include "bitr3d.mm"
include "pm2.61dane.mm"

theorem tgcolg
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


  assert |- ( ph -> ( ( Z e. ( X L Y ) \/ X = Y ) <-> ( Z e. ( X I Y ) \/ X e. ( Z I Y ) \/ Y e. ( X I Z ) ) ) )

  proof
    wph
    cZ
    cX
    cY
    cL
    co
    wcel
    #
    cX
    cY
    wceq
    #
    wo
    #
    cZ
    cX
    cY
    cI
    co
    wcel
    #
    cX
    cZ
    cY
    cI
    co
    #
    wcel
    #
    cY
    cX
    cZ
    cI
    co
    wcel
    #
    w3o
    #
    wb
    cX
    cY
    wph
    @1
    wa
    #
    @2
    @7
    @8
    @1
    @0
    wph
    @1
    simpr
    #
    olcd
    @8
    @5
    @3
    @6
    @8
    cX
    cZ
    cX
    cI
    co
    @4
    @8
    cZ
    cX
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    tglngval.p
    @10
    eqid
    tglngval.i
    wph
    cG
    cstrkg
    wcel
    #
    @1
    tglngval.g
    adantr
    wph
    cZ
    cP
    wcel
    #
    @1
    tgcolg.z
    adantr
    wph
    cX
    cP
    wcel
    #
    @1
    tglngval.x
    adantr
    tgbtwntriv2
    @8
    cX
    cY
    cZ
    cI
    @9
    oveq2d
    eleqtrd
    3mix2d
    2thd
    wph
    cX
    cY
    wne
    #
    wa
    #
    @0
    @2
    @7
    @15
    @0
    @1
    @0
    wo
    #
    @2
    @15
    @1
    wn
    @0
    @16
    wb
    @15
    cX
    cY
    wph
    @14
    simpr
    #
    neneqd
    @1
    @0
    biorf
    syl
    @1
    @0
    orcom
    syl6bb
    @15
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
    @11
    @14
    tglngval.g
    adantr
    wph
    @13
    @14
    tglngval.x
    adantr
    wph
    cY
    cP
    wcel
    @14
    tglngval.y
    adantr
    @17
    wph
    @12
    @14
    tgcolg.z
    adantr
    tgellng
    bitr3d
    pm2.61dane
end
