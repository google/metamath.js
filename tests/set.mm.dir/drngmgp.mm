include "cdr.mm"
include "wcel.mm"
include "crg.mm"
include "cgrp.mm"
include "isdrng2.mm"
include "simprbi.mm"

theorem drngmgp
  let cB: class B
  let cR: class R
  let cG: class G
  let c.0: class .0.
  assume drngmgp.b: |- B = ( Base ` R )
  assume drngmgp.z: |- .0. = ( 0g ` R )
  assume drngmgp.g: |- G = ( ( mulGrp ` R ) |`s ( B \ { .0. } ) )


  assert |- ( R e. DivRing -> G e. Grp )

  proof
    cR
    cdr
    wcel
    cR
    crg
    wcel
    cG
    cgrp
    wcel
    cB
    cR
    cG
    c.0
    drngmgp.b
    drngmgp.z
    drngmgp.g
    isdrng2
    simprbi
end
