include "ncolcom.mm"
include "ncolne1.mm"

theorem ncolne2
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


  assert |- ( ph -> X =/= Z )

  proof
    wph
    cB
    cG
    cI
    cL
    cX
    cZ
    cY
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    tglineelsb2.g
    ncolne.x
    ncolne.z
    ncolne.y
    wph
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
    tglineelsb2.g
    ncolne.y
    ncolne.z
    ncolne.x
    ncolne.2
    ncolcom
    ncolne1
end
