include "crg.mm"
include "wcel.mm"
include "cgrp.mm"
include "co.mm"
include "ringgrp.mm"
include "grpcl.mm"
include "syl3an1.mm"

theorem ringacl
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cX: class X
  let cY: class Y
  assume ringacl.b: |- B = ( Base ` R )
  assume ringacl.p: |- .+ = ( +g ` R )


  assert |- ( ( R e. Ring /\ X e. B /\ Y e. B ) -> ( X .+ Y ) e. B )

  proof
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.pl
    co
    cB
    wcel
    cR
    ringgrp
    cB
    c.pl
    cR
    cX
    cY
    ringacl.b
    ringacl.p
    grpcl
    syl3an1
end
