include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "w3o.mm"
include "3orcomb.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "tgbtwncomb.mm"
include "3orbi123d.mm"
include "syl5bb.mm"
include "tgcolg.mm"
include "3bitr4d.mm"
include "mpbid.mm"

theorem colcom
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
  assume colrot: |- ( ph -> ( Z e. ( X L Y ) \/ X = Y ) )


  assert |- ( ph -> ( Z e. ( Y L X ) \/ Y = X ) )

  proof
    wph
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
    #
    cZ
    cY
    cX
    cL
    co
    wcel
    cY
    cX
    wceq
    wo
    #
    colrot
    wph
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
    cZ
    cY
    cX
    cI
    co
    wcel
    #
    cY
    cZ
    cX
    cI
    co
    wcel
    #
    cX
    cY
    cZ
    cI
    co
    wcel
    #
    w3o
    #
    @0
    @1
    @5
    @2
    @4
    @3
    w3o
    wph
    @9
    @2
    @3
    @4
    3orcomb
    wph
    @2
    @6
    @4
    @7
    @3
    @8
    wph
    cX
    cZ
    cY
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
    #
    tglngval.i
    tglngval.g
    tglngval.x
    tgcolg.z
    tglngval.y
    tgbtwncomb
    wph
    cX
    cY
    cZ
    cP
    cG
    cI
    @10
    tglngval.p
    @11
    tglngval.i
    tglngval.g
    tglngval.x
    tglngval.y
    tgcolg.z
    tgbtwncomb
    wph
    cZ
    cX
    cY
    cP
    cG
    cI
    @10
    tglngval.p
    @11
    tglngval.i
    tglngval.g
    tgcolg.z
    tglngval.x
    tglngval.y
    tgbtwncomb
    3orbi123d
    syl5bb
    wph
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
    tglngval.g
    tglngval.x
    tglngval.y
    tgcolg.z
    tgcolg
    wph
    cP
    cG
    cI
    cL
    cY
    cX
    cZ
    tglngval.p
    tglngval.l
    tglngval.i
    tglngval.g
    tglngval.y
    tglngval.x
    tgcolg.z
    tgcolg
    3bitr4d
    mpbid
end
