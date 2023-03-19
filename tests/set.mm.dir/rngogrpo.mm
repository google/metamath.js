include "crngo.mm"
include "wcel.mm"
include "cablo.mm"
include "cgr.mm"
include "rngoablo.mm"
include "ablogrpo.mm"
include "syl.mm"

theorem rngogrpo
  let cR: class R
  let cG: class G
  assume ringgrp.1: |- G = ( 1st ` R )


  assert |- ( R e. RingOps -> G e. GrpOp )

  proof
    cR
    crngo
    wcel
    cG
    cablo
    wcel
    cG
    cgr
    wcel
    cR
    cG
    ringgrp.1
    rngoablo
    cG
    ablogrpo
    syl
end
