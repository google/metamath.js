include "crngo.mm"
include "wcel.mm"
include "cgr.mm"
include "rngogrpo.mm"
include "grpoidcl.mm"
include "syl.mm"

theorem rngo0cl
  let cR: class R
  let cG: class G
  let cX: class X
  let cZ: class Z
  assume ring0cl.1: |- G = ( 1st ` R )
  assume ring0cl.2: |- X = ran G
  assume ring0cl.3: |- Z = ( GId ` G )


  assert |- ( R e. RingOps -> Z e. X )

  proof
    cR
    crngo
    wcel
    cG
    cgr
    wcel
    cZ
    cX
    wcel
    cR
    cG
    ring0cl.1
    rngogrpo
    cZ
    cG
    cX
    ring0cl.2
    ring0cl.3
    grpoidcl
    syl
end
