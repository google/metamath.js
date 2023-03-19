include "cn.mm"
include "cc.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cc0.mm"
include "cfzo.mm"
include "ffvelrnd.mm"
include "cnex.mm"
include "nnex.mm"
include "elmap.mm"
include "sylib.mm"

theorem breprexplemb
  let wph: wff ph
  let cS: class S
  let cL: class L
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vm: setvar m
  let vs: setvar s
  let vt: setvar t
  let va: setvar a
  let vb: setvar b
  assume breprexp.n: |- ( ph -> N e. NN0 )
  assume breprexp.s: |- ( ph -> S e. NN0 )
  assume breprexp.z: |- ( ph -> Z e. CC )
  assume breprexp.h: |- ( ph -> L : ( 0 ..^ S ) --> ( CC ^m NN ) )
  assume breprexplemb.x: |- ( ph -> X e. ( 0 ..^ S ) )
  assume breprexplemb.y: |- ( ph -> Y e. NN )


  assert |- ( ph -> ( ( L ` X ) ` Y ) e. CC )

  proof
    wph
    cn
    cc
    cY
    cX
    cL
    cfv
    #
    wph
    @0
    cc
    cn
    cmap
    co
    #
    wcel
    cn
    cc
    @0
    wf
    wph
    cc0
    cS
    cfzo
    co
    @1
    cX
    cL
    breprexp.h
    breprexplemb.x
    ffvelrnd
    cc
    cn
    @0
    cnex
    nnex
    elmap
    sylib
    breprexplemb.y
    ffvelrnd
end
