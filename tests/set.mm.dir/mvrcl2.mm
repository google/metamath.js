include "mvrf.mm"
include "ffvelrnd.mm"

theorem mvrcl2
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mvrf.s: |- S = ( I mPwSer R )
  assume mvrf.v: |- V = ( I mVar R )
  assume mvrf.b: |- B = ( Base ` S )
  assume mvrf.i: |- ( ph -> I e. W )
  assume mvrf.r: |- ( ph -> R e. Ring )
  assume mvrcl2.x: |- ( ph -> X e. I )


  assert |- ( ph -> ( V ` X ) e. B )

  proof
    wph
    cI
    cB
    cX
    cV
    wph
    cB
    cR
    cS
    cI
    cV
    cW
    mvrf.s
    mvrf.v
    mvrf.b
    mvrf.i
    mvrf.r
    mvrf
    mvrcl2.x
    ffvelrnd
end
