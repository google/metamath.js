include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "csn.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "lmodvsubcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "lspsnneg.mm"
include "syl2anc.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "syl.mm"
include "grpinvsub.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"

theorem lspsnsub
  let wph: wff ph
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspsnsub.v: |- V = ( Base ` W )
  assume lspsnsub.s: |- .- = ( -g ` W )
  assume lspsnsub.n: |- N = ( LSpan ` W )
  assume lspsnsub.w: |- ( ph -> W e. LMod )
  assume lspsnsub.x: |- ( ph -> X e. V )
  assume lspsnsub.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( N ` { ( X .- Y ) } ) = ( N ` { ( Y .- X ) } ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    #
    cW
    cminusg
    cfv
    #
    cfv
    #
    csn
    #
    cN
    cfv
    #
    @0
    csn
    cN
    cfv
    #
    cY
    cX
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    wph
    cW
    clmod
    wcel
    #
    @0
    cV
    wcel
    #
    @4
    @5
    wceq
    lspsnsub.w
    wph
    @8
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @9
    lspsnsub.w
    lspsnsub.x
    lspsnsub.y
    c.mi
    cV
    cW
    cX
    cY
    lspsnsub.v
    lspsnsub.s
    lmodvsubcl
    syl3anc
    @1
    cN
    cV
    cW
    @0
    lspsnsub.v
    @1
    eqid
    #
    lspsnsub.n
    lspsnneg
    syl2anc
    wph
    @3
    @7
    cN
    wph
    @2
    @6
    wph
    cW
    cgrp
    wcel
    #
    @10
    @11
    @2
    @6
    wceq
    wph
    @8
    @13
    lspsnsub.w
    cW
    lmodgrp
    syl
    lspsnsub.x
    lspsnsub.y
    cV
    cW
    c.mi
    @1
    cX
    cY
    lspsnsub.v
    lspsnsub.s
    @12
    grpinvsub
    syl3anc
    sneqd
    fveq2d
    eqtr3d
end
