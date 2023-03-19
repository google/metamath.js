include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "cabl.mm"
include "wcel.mm"
include "wceq.mm"
include "ablsub4.mm"
include "syl122anc.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "syl.mm"
include "eqid.mm"
include "grpsubid.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "grplid.mm"
include "3eqtrd.mm"

theorem ablpnpcan
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
  assume ablpnpcan.g: |- ( ph -> G e. Abel )
  assume ablpnpcan.x: |- ( ph -> X e. B )
  assume ablpnpcan.y: |- ( ph -> Y e. B )
  assume ablpnpcan.z: |- ( ph -> Z e. B )


  assert |- ( ph -> ( ( X .+ Y ) .- ( X .+ Z ) ) = ( Y .- Z ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    cX
    cZ
    c.pl
    co
    c.mi
    co
    #
    cX
    cX
    c.mi
    co
    #
    cY
    cZ
    c.mi
    co
    #
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    @2
    c.pl
    co
    #
    @2
    wph
    cG
    cabl
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
    @7
    cZ
    cB
    wcel
    #
    @0
    @3
    wceq
    ablsubsub.g
    ablsubsub.x
    ablsubsub.y
    ablsubsub.x
    ablsubsub.z
    cB
    c.pl
    cG
    c.mi
    cZ
    cX
    cY
    cX
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    ablsub4
    syl122anc
    wph
    @1
    @4
    @2
    c.pl
    wph
    cG
    cgrp
    wcel
    #
    @7
    @1
    @4
    wceq
    wph
    @6
    @10
    ablsubsub.g
    cG
    ablgrp
    syl
    #
    ablsubsub.x
    cB
    cG
    c.mi
    cX
    @4
    ablsubadd.b
    @4
    eqid
    #
    ablsubadd.m
    grpsubid
    syl2anc
    oveq1d
    wph
    @10
    @2
    cB
    wcel
    #
    @5
    @2
    wceq
    @11
    wph
    @10
    @8
    @9
    @13
    @11
    ablsubsub.y
    ablsubsub.z
    cB
    cG
    c.mi
    cY
    cZ
    ablsubadd.b
    ablsubadd.m
    grpsubcl
    syl3anc
    cB
    c.pl
    cG
    @2
    @4
    ablsubadd.b
    ablsubadd.p
    @12
    grplid
    syl2anc
    3eqtrd
end
