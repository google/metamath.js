include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "c0.mm"
include "wne.mm"
include "lmodfgrp.mm"
include "grpbn0.mm"
include "syl.mm"

theorem lmodsn0
  let cB: class B
  let cF: class F
  let cW: class W
  assume lmodsn0.f: |- F = ( Scalar ` W )
  assume lmodsn0.b: |- B = ( Base ` F )


  assert |- ( W e. LMod -> B =/= (/) )

  proof
    cW
    clmod
    wcel
    cF
    cgrp
    wcel
    cB
    c0
    wne
    cF
    cW
    lmodsn0.f
    lmodfgrp
    cB
    cF
    lmodsn0.b
    grpbn0
    syl
end
