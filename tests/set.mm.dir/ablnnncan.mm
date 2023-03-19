include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqid.mm"
include "cgrp.mm"
include "wcel.mm"
include "cabl.mm"
include "ablgrp.mm"
include "syl.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "ablsubsub4.mm"
include "wceq.mm"
include "ablcom.mm"
include "ablpncan3.mm"
include "syl12anc.mm"
include "eqtrd.mm"
include "oveq2d.mm"

theorem ablnnncan
  let wph: wff ph
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ablnncan.b: |- B = ( Base ` G )
  assume ablnncan.m: |- .- = ( -g ` G )
  assume ablnncan.g: |- ( ph -> G e. Abel )
  assume ablnncan.x: |- ( ph -> X e. B )
  assume ablnncan.y: |- ( ph -> Y e. B )
  assume ablsub32.z: |- ( ph -> Z e. B )


  assert |- ( ph -> ( ( X .- ( Y .- Z ) ) .- Z ) = ( X .- Y ) )

  proof
    wph
    cX
    cY
    cZ
    c.mi
    co
    #
    c.mi
    co
    cZ
    c.mi
    co
    cX
    @0
    cZ
    cG
    cplusg
    cfv
    #
    co
    #
    c.mi
    co
    cX
    cY
    c.mi
    co
    wph
    cB
    @1
    cG
    c.mi
    cX
    @0
    cZ
    ablnncan.b
    @1
    eqid
    #
    ablnncan.m
    ablnncan.g
    ablnncan.x
    wph
    cG
    cgrp
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
    cB
    wcel
    #
    wph
    cG
    cabl
    wcel
    #
    @4
    ablnncan.g
    cG
    ablgrp
    syl
    ablnncan.y
    ablsub32.z
    cB
    cG
    c.mi
    cY
    cZ
    ablnncan.b
    ablnncan.m
    grpsubcl
    syl3anc
    #
    ablsub32.z
    ablsubsub4
    wph
    @2
    cY
    cX
    c.mi
    wph
    @2
    cZ
    @0
    @1
    co
    #
    cY
    wph
    @8
    @7
    @6
    @2
    @10
    wceq
    ablnncan.g
    @9
    ablsub32.z
    cB
    @1
    cG
    @0
    cZ
    ablnncan.b
    @3
    ablcom
    syl3anc
    wph
    @8
    @6
    @5
    @10
    cY
    wceq
    ablnncan.g
    ablsub32.z
    ablnncan.y
    cB
    @1
    cG
    c.mi
    cZ
    cY
    ablnncan.b
    @3
    ablnncan.m
    ablpncan3
    syl12anc
    eqtrd
    oveq2d
    eqtrd
end
