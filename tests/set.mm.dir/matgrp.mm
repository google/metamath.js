include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "clmod.mm"
include "cgrp.mm"
include "matlmod.mm"
include "lmodgrp.mm"
include "syl.mm"

theorem matgrp
  let cA: class A
  let cR: class R
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume matlmod.a: |- A = ( N Mat R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> A e. Grp )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    cA
    clmod
    wcel
    cA
    cgrp
    wcel
    cA
    cR
    cN
    matlmod.a
    matlmod
    cA
    lmodgrp
    syl
end
