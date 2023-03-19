include "colrot1.mm"

theorem colrot2
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


  assert |- ( ph -> ( Y e. ( Z L X ) \/ Z = X ) )

  proof
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
    colrot
    colrot1
    colrot1
end
