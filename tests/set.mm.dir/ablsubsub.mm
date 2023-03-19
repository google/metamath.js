include "co.mm"
include "cgrp.mm"
include "wcel.mm"
include "wceq.mm"
include "cabl.mm"
include "ablgrp.mm"
include "syl.mm"
include "grpsubsub.mm"
include "syl13anc.mm"
include "grpaddsubass.mm"
include "abladdsub.mm"
include "3eqtr2d.mm"

theorem ablsubsub
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ablsubadd.b: |- B = ( Base ` G )
  assume ablsubadd.p: |- .+ = ( +g ` G )
  assume ablsubadd.m: |- .- = ( -g ` G )
  assume ablsubsub.g: |- ( ph -> G e. Abel )
  assume ablsubsub.x: |- ( ph -> X e. B )
  assume ablsubsub.y: |- ( ph -> Y e. B )
  assume ablsubsub.z: |- ( ph -> Z e. B )


  assert |- ( ph -> ( X .- ( Y .- Z ) ) = ( ( X .- Y ) .+ Z ) )

  proof
    wph
    cX
    cY
    cZ
    c.mi
    co
    c.mi
    co
    #
    cX
    cZ
    cY
    c.mi
    co
    c.pl
    co
    #
    cX
    cZ
    c.pl
    co
    cY
    c.mi
    co
    #
    cX
    cY
    c.mi
    co
    cZ
    c.pl
    co
    #
    wph
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    @0
    @1
    wceq
    wph
    cG
    cabl
    wcel
    #
    @4
    ablsubsub.g
    cG
    ablgrp
    syl
    #
    ablsubsub.x
    ablsubsub.y
    ablsubsub.z
    cB
    c.pl
    cG
    c.mi
    cX
    cY
    cZ
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    grpsubsub
    syl13anc
    wph
    @4
    @5
    @7
    @6
    @2
    @1
    wceq
    @9
    ablsubsub.x
    ablsubsub.z
    ablsubsub.y
    cB
    c.pl
    cG
    c.mi
    cX
    cZ
    cY
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    grpaddsubass
    syl13anc
    wph
    @8
    @5
    @7
    @6
    @2
    @3
    wceq
    ablsubsub.g
    ablsubsub.x
    ablsubsub.z
    ablsubsub.y
    cB
    c.pl
    cG
    c.mi
    cX
    cZ
    cY
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    abladdsub
    syl13anc
    3eqtr2d
end
