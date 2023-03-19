include "co.mm"
include "cgrp.mm"
include "wcel.mm"
include "cabl.mm"
include "ablgrp.mm"
include "syl.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "ablsub32.mm"
include "ablnncan.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem ablnnncan1
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


  assert |- ( ph -> ( ( X .- Y ) .- ( X .- Z ) ) = ( Z .- Y ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    cX
    cZ
    c.mi
    co
    #
    c.mi
    co
    cX
    @0
    c.mi
    co
    #
    cY
    c.mi
    co
    cZ
    cY
    c.mi
    co
    wph
    cB
    cG
    c.mi
    cX
    cY
    @0
    ablnncan.b
    ablnncan.m
    ablnncan.g
    ablnncan.x
    ablnncan.y
    wph
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    cZ
    cB
    wcel
    @0
    cB
    wcel
    wph
    cG
    cabl
    wcel
    @2
    ablnncan.g
    cG
    ablgrp
    syl
    ablnncan.x
    ablsub32.z
    cB
    cG
    c.mi
    cX
    cZ
    ablnncan.b
    ablnncan.m
    grpsubcl
    syl3anc
    ablsub32
    wph
    @1
    cZ
    cY
    c.mi
    wph
    cB
    cG
    c.mi
    cX
    cZ
    ablnncan.b
    ablnncan.m
    ablnncan.g
    ablnncan.x
    ablsub32.z
    ablnncan
    oveq1d
    eqtrd
end
