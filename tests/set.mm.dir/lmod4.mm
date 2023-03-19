include "clmod.mm"
include "wcel.mm"
include "ccmn.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "lmodcmn.mm"
include "cmn4.mm"
include "syl3an1.mm"

theorem lmod4
  let c.pl: class .+
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lmod4.v: |- V = ( Base ` W )
  assume lmod4.p: |- .+ = ( +g ` W )


  assert |- ( ( W e. LMod /\ ( X e. V /\ Y e. V ) /\ ( Z e. V /\ U e. V ) ) -> ( ( X .+ Y ) .+ ( Z .+ U ) ) = ( ( X .+ Z ) .+ ( Y .+ U ) ) )

  proof
    cW
    clmod
    wcel
    cW
    ccmn
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    wa
    cZ
    cV
    wcel
    cU
    cV
    wcel
    wa
    cX
    cY
    c.pl
    co
    cZ
    cU
    c.pl
    co
    c.pl
    co
    cX
    cZ
    c.pl
    co
    cY
    cU
    c.pl
    co
    c.pl
    co
    wceq
    cW
    lmodcmn
    cV
    c.pl
    cW
    cU
    cX
    cY
    cZ
    lmod4.v
    lmod4.p
    cmn4
    syl3an1
end
