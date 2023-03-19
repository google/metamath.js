include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "clmod.mm"
include "wcel.mm"
include "wb.mm"
include "lmodsubeq0.mm"
include "syl3anc.mm"
include "sneq.mm"
include "fveq2d.mm"
include "syl6bi.mm"
include "necon3d.mm"
include "mpd.mm"

theorem lspsnsubn0
  let wph: wff ph
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspsnsubn0.v: |- V = ( Base ` W )
  assume lspsnsubn0.o: |- .0. = ( 0g ` W )
  assume lspsnsubn0.m: |- .- = ( -g ` W )
  assume lspsnsubn0.w: |- ( ph -> W e. LMod )
  assume lspsnsubn0.x: |- ( ph -> X e. V )
  assume lspsnsubn0.y: |- ( ph -> Y e. V )
  assume lspsnsubn0.e: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )


  assert |- ( ph -> ( X .- Y ) =/= .0. )

  proof
    wph
    cX
    csn
    #
    cN
    cfv
    #
    cY
    csn
    #
    cN
    cfv
    #
    wne
    cX
    cY
    c.mi
    co
    #
    c.0
    wne
    lspsnsubn0.e
    wph
    @4
    c.0
    @1
    @3
    wph
    @4
    c.0
    wceq
    #
    cX
    cY
    wceq
    #
    @1
    @3
    wceq
    wph
    cW
    clmod
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    @5
    @6
    wb
    lspsnsubn0.w
    lspsnsubn0.x
    lspsnsubn0.y
    cX
    cY
    c.mi
    cV
    cW
    c.0
    lspsnsubn0.v
    lspsnsubn0.o
    lspsnsubn0.m
    lmodsubeq0
    syl3anc
    @6
    @0
    @2
    cN
    cX
    cY
    sneq
    fveq2d
    syl6bi
    necon3d
    mpd
end
