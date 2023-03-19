include "wceq.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "tgbtwntriv1.mm"
include "simpr.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "btwncolg1.mm"
include "mtand.mm"
include "neqned.mm"

theorem ncolne1
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume ncolne.x: |- ( ph -> X e. B )
  assume ncolne.y: |- ( ph -> Y e. B )
  assume ncolne.z: |- ( ph -> Z e. B )
  assume ncolne.2: |- ( ph -> -. ( X e. ( Y L Z ) \/ Y = Z ) )


  assert |- ( ph -> X =/= Y )

  proof
    wph
    cX
    cY
    wph
    cX
    cY
    wceq
    #
    cX
    cY
    cZ
    cL
    co
    wcel
    cY
    cZ
    wceq
    wo
    ncolne.2
    wph
    @0
    wa
    #
    cB
    cG
    cI
    cL
    cY
    cZ
    cX
    tglineelsb2.p
    tglineelsb2.l
    tglineelsb2.i
    wph
    cG
    cstrkg
    wcel
    @0
    tglineelsb2.g
    adantr
    #
    wph
    cY
    cB
    wcel
    @0
    ncolne.y
    adantr
    wph
    cZ
    cB
    wcel
    @0
    ncolne.z
    adantr
    #
    wph
    cX
    cB
    wcel
    @0
    ncolne.x
    adantr
    #
    @1
    cX
    cX
    cZ
    cI
    co
    cY
    cZ
    cI
    co
    @1
    cX
    cZ
    cB
    cG
    cI
    cG
    cds
    cfv
    #
    tglineelsb2.p
    @5
    eqid
    tglineelsb2.i
    @2
    @4
    @3
    tgbtwntriv1
    @1
    cX
    cY
    cZ
    cI
    wph
    @0
    simpr
    oveq1d
    eleqtrd
    btwncolg1
    mtand
    neqned
end
