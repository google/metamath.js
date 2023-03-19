include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "cgrp.mm"
include "cabl.mm"
include "ablgrp.mm"
include "syl.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "grpinvcl.mm"
include "ablsubsub.mm"
include "grpsubinv.mm"
include "oveq2d.mm"
include "3eqtr2d.mm"

theorem ablsubsub4
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


  assert |- ( ph -> ( ( X .- Y ) .- Z ) = ( X .- ( Y .+ Z ) ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    #
    cZ
    c.mi
    co
    #
    @0
    cZ
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    cX
    cY
    @3
    c.mi
    co
    #
    c.mi
    co
    cX
    cY
    cZ
    c.pl
    co
    #
    c.mi
    co
    wph
    @0
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    @1
    @4
    wceq
    wph
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    @7
    wph
    cG
    cabl
    wcel
    @9
    ablsubsub.g
    cG
    ablgrp
    syl
    #
    ablsubsub.x
    ablsubsub.y
    cB
    cG
    c.mi
    cX
    cY
    ablsubadd.b
    ablsubadd.m
    grpsubcl
    syl3anc
    ablsubsub.z
    cB
    c.pl
    cG
    @2
    c.mi
    @0
    cZ
    ablsubadd.b
    ablsubadd.p
    @2
    eqid
    #
    ablsubadd.m
    grpsubval
    syl2anc
    wph
    cB
    c.pl
    cG
    c.mi
    cX
    cY
    @3
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    ablsubsub.g
    ablsubsub.x
    ablsubsub.y
    wph
    @9
    @8
    @3
    cB
    wcel
    @10
    ablsubsub.z
    cB
    cG
    @2
    cZ
    ablsubadd.b
    @11
    grpinvcl
    syl2anc
    ablsubsub
    wph
    @5
    @6
    cX
    c.mi
    wph
    cB
    c.pl
    cG
    c.mi
    @2
    cY
    cZ
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    @11
    @10
    ablsubsub.y
    ablsubsub.z
    grpsubinv
    oveq2d
    3eqtr2d
end
