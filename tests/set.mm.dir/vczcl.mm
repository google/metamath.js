include "cvc.mm"
include "wcel.mm"
include "cgr.mm"
include "vcgrp.mm"
include "grpoidcl.mm"
include "syl.mm"

theorem vczcl
  let cG: class G
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume vczcl.1: |- G = ( 1st ` W )
  assume vczcl.2: |- X = ran G
  assume vczcl.3: |- Z = ( GId ` G )


  assert |- ( W e. CVecOLD -> Z e. X )

  proof
    cW
    cvc
    wcel
    cG
    cgr
    wcel
    cZ
    cX
    wcel
    cG
    cW
    vczcl.1
    vcgrp
    cZ
    cG
    cX
    vczcl.2
    vczcl.3
    grpoidcl
    syl
end
