include "cgr3id.mm"
include "tgfscgr.mm"

theorem lncgr
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
  assume lncgr.1: |- ( ph -> X =/= Y )
  assume lncgr.2: |- ( ph -> ( Y e. ( X L Z ) \/ X = Z ) )
  assume lncgr.3: |- ( ph -> ( X .- A ) = ( X .- B ) )
  assume lncgr.4: |- ( ph -> ( Y .- A ) = ( Y .- B ) )


  assert |- ( ph -> ( Z .- A ) = ( Z .- B ) )

  proof
    wph
    cX
    cY
    cZ
    cB
    cP
    c.sm
    cA
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
    tglngval.g
    tglngval.x
    tglngval.y
    tgcolg.z
    lnxfr.r
    tglngval.x
    tglngval.y
    lnxfr.d
    lnxfr.a
    tgcolg.z
    lnxfr.b
    lncgr.2
    wph
    cX
    cY
    cZ
    cP
    c.sm
    cG
    cI
    c.mi
    tglngval.p
    lnxfr.d
    tglngval.i
    lnxfr.r
    tglngval.g
    tglngval.x
    tglngval.y
    tgcolg.z
    cgr3id
    lncgr.3
    lncgr.4
    lncgr.1
    tgfscgr
end
