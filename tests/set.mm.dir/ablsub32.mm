include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cabl.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "ablsubsub4.mm"
include "3eqtr4d.mm"

theorem ablsub32
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


  assert |- ( ph -> ( ( X .- Y ) .- Z ) = ( ( X .- Z ) .- Y ) )

  proof
    wph
    cX
    cY
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
    cZ
    cY
    @0
    co
    #
    c.mi
    co
    cX
    cY
    c.mi
    co
    cZ
    c.mi
    co
    cX
    cZ
    c.mi
    co
    cY
    c.mi
    co
    wph
    @1
    @2
    cX
    c.mi
    wph
    cG
    cabl
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    @1
    @2
    wceq
    ablnncan.g
    ablnncan.y
    ablsub32.z
    cB
    @0
    cG
    cY
    cZ
    ablnncan.b
    @0
    eqid
    #
    ablcom
    syl3anc
    oveq2d
    wph
    cB
    @0
    cG
    c.mi
    cX
    cY
    cZ
    ablnncan.b
    @3
    ablnncan.m
    ablnncan.g
    ablnncan.x
    ablnncan.y
    ablsub32.z
    ablsubsub4
    wph
    cB
    @0
    cG
    c.mi
    cX
    cZ
    cY
    ablnncan.b
    @3
    ablnncan.m
    ablnncan.g
    ablnncan.x
    ablsub32.z
    ablnncan.y
    ablsubsub4
    3eqtr4d
end
