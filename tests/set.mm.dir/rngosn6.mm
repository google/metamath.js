include "crngo.mm"
include "wcel.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "wb.mm"
include "rngo0cl.mm"
include "rngosn4.mm"
include "mpdan.mm"

theorem rngosn6
  let cR: class R
  let cG: class G
  let cX: class X
  let cZ: class Z
  assume on1el3.1: |- G = ( 1st ` R )
  assume on1el3.2: |- X = ran G
  assume on1el3.3: |- Z = ( GId ` G )


  assert |- ( R e. RingOps -> ( X ~~ 1o <-> R = <. { <. <. Z , Z >. , Z >. } , { <. <. Z , Z >. , Z >. } >. ) )

  proof
    cR
    crngo
    wcel
    cZ
    cX
    wcel
    cX
    c1o
    cen
    wbr
    cR
    cZ
    cZ
    cop
    cZ
    cop
    csn
    #
    @0
    cop
    wceq
    wb
    cR
    cG
    cX
    cZ
    on1el3.1
    on1el3.2
    on1el3.3
    rngo0cl
    cZ
    cR
    cG
    cX
    on1el3.1
    on1el3.2
    rngosn4
    mpdan
end
