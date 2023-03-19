include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "co.mm"
include "lmodfgrp.mm"
include "grpcl.mm"
include "syl3an1.mm"

theorem lmodacl
  let c.pl: class .+
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lmodacl.f: |- F = ( Scalar ` W )
  assume lmodacl.k: |- K = ( Base ` F )
  assume lmodacl.p: |- .+ = ( +g ` F )


  assert |- ( ( W e. LMod /\ X e. K /\ Y e. K ) -> ( X .+ Y ) e. K )

  proof
    cW
    clmod
    wcel
    cF
    cgrp
    wcel
    cX
    cK
    wcel
    cY
    cK
    wcel
    cX
    cY
    c.pl
    co
    cK
    wcel
    cF
    cW
    lmodacl.f
    lmodfgrp
    cK
    c.pl
    cF
    cX
    cY
    lmodacl.k
    lmodacl.p
    grpcl
    syl3an1
end
