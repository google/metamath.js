include "cvc.mm"
include "wcel.mm"
include "cablo.mm"
include "cgr.mm"
include "vcablo.mm"
include "ablogrpo.mm"
include "syl.mm"

theorem vcgrp
  let cG: class G
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume vcabl.1: |- G = ( 1st ` W )


  assert |- ( W e. CVecOLD -> G e. GrpOp )

  proof
    cW
    cvc
    wcel
    cG
    cablo
    wcel
    cG
    cgr
    wcel
    cG
    cW
    vcabl.1
    vcablo
    cG
    ablogrpo
    syl
end
