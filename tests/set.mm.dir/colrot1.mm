include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "w3o.mm"
include "3orrot.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "tgbtwncomb.mm"
include "biidd.mm"
include "3orbi123d.mm"
include "syl5bb.mm"
include "tgcolg.mm"
include "3bitr4d.mm"
include "mpbid.mm"

theorem colrot1
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


  assert |- ( ph -> ( X e. ( Y L Z ) \/ Y = Z ) )

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
    cX
    cY
    cZ
    cI
    co
    wcel
    #
    @4
    cZ
    cY
    cX
    cI
    co
    wcel
    #
    w3o
    #
    @0
    @1
    @5
    @3
    @4
    @2
    w3o
    wph
    @8
    @2
    @3
    @4
    3orrot
    wph
    @3
    @6
    @4
    @4
    @2
    @7
    wph
    cZ
    cX
    cY
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    tglngval.p
    @9
    eqid
    #
    tglngval.i
    tglngval.g
    tgcolg.z
    tglngval.x
    tglngval.y
    tgbtwncomb
    wph
    @4
    biidd
    wph
    cX
    cZ
    cY
    cP
    cG
    cI
    @9
    tglngval.p
    @10
    tglngval.i
    tglngval.g
    tglngval.x
    tgcolg.z
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
    cZ
    cX
    tglngval.p
    tglngval.l
    tglngval.i
    tglngval.g
    tglngval.y
    tgcolg.z
    tglngval.x
    tgcolg
    3bitr4d
    mpbid
end
