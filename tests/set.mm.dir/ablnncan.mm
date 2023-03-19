include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "c0g.mm"
include "eqid.mm"
include "ablsubsub.mm"
include "cgrp.mm"
include "wcel.mm"
include "wceq.mm"
include "cabl.mm"
include "ablgrp.mm"
include "syl.mm"
include "grpsubid.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "grplid.mm"
include "3eqtrd.mm"

theorem ablnncan
  let wph: wff ph
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  assume ablnncan.b: |- B = ( Base ` G )
  assume ablnncan.m: |- .- = ( -g ` G )
  assume ablnncan.g: |- ( ph -> G e. Abel )
  assume ablnncan.x: |- ( ph -> X e. B )
  assume ablnncan.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X .- ( X .- Y ) ) = Y )

  proof
    wph
    cX
    cX
    cY
    c.mi
    co
    c.mi
    co
    cX
    cX
    c.mi
    co
    #
    cY
    cG
    cplusg
    cfv
    #
    co
    cG
    c0g
    cfv
    #
    cY
    @1
    co
    #
    cY
    wph
    cB
    @1
    cG
    c.mi
    cX
    cX
    cY
    ablnncan.b
    @1
    eqid
    #
    ablnncan.m
    ablnncan.g
    ablnncan.x
    ablnncan.x
    ablnncan.y
    ablsubsub
    wph
    @0
    @2
    cY
    @1
    wph
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    @0
    @2
    wceq
    wph
    cG
    cabl
    wcel
    @5
    ablnncan.g
    cG
    ablgrp
    syl
    #
    ablnncan.x
    cB
    cG
    c.mi
    cX
    @2
    ablnncan.b
    @2
    eqid
    #
    ablnncan.m
    grpsubid
    syl2anc
    oveq1d
    wph
    @5
    cY
    cB
    wcel
    @3
    cY
    wceq
    @6
    ablnncan.y
    cB
    @1
    cG
    cY
    @2
    ablnncan.b
    @4
    @7
    grplid
    syl2anc
    3eqtrd
end
