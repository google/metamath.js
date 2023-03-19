include "cgrp.mm"
include "wcel.mm"
include "ccmn.mm"
include "cabl.mm"
include "wf.mm"
include "wss.mm"
include "cv.mm"
include "ablgrp.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "prdsgrpd.mm"
include "ablcmn.mm"
include "prdscmnd.mm"
include "isabl.mm"
include "sylanbrc.mm"

theorem prdsabld
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vc: setvar c
  let va: setvar a
  let vb: setvar b
  assume prdscmnd.y: |- Y = ( S Xs_ R )
  assume prdscmnd.i: |- ( ph -> I e. W )
  assume prdscmnd.s: |- ( ph -> S e. V )
  assume prdsgabld.r: |- ( ph -> R : I --> Abel )


  assert |- ( ph -> Y e. Abel )

  proof
    wph
    cY
    cgrp
    wcel
    cY
    ccmn
    wcel
    cY
    cabl
    wcel
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdscmnd.y
    prdscmnd.i
    prdscmnd.s
    wph
    cI
    cabl
    cR
    wf
    #
    cabl
    cgrp
    wss
    cI
    cgrp
    cR
    wf
    prdsgabld.r
    va
    cabl
    cgrp
    va
    cv
    #
    ablgrp
    ssriv
    cI
    cabl
    cgrp
    cR
    fss
    sylancl
    prdsgrpd
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdscmnd.y
    prdscmnd.i
    prdscmnd.s
    wph
    @0
    cabl
    ccmn
    wss
    cI
    ccmn
    cR
    wf
    prdsgabld.r
    va
    cabl
    ccmn
    @1
    ablcmn
    ssriv
    cI
    cabl
    ccmn
    cR
    fss
    sylancl
    prdscmnd
    cY
    isabl
    sylanbrc
end
