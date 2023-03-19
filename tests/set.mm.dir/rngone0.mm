include "crngo.mm"
include "wcel.mm"
include "cgr.mm"
include "c0.mm"
include "wne.mm"
include "rngogrpo.mm"
include "grpon0.mm"
include "syl.mm"

theorem rngone0
  let cR: class R
  let cG: class G
  let cX: class X
  assume rngone0.1: |- G = ( 1st ` R )
  assume rngone0.2: |- X = ran G


  assert |- ( R e. RingOps -> X =/= (/) )

  proof
    cR
    crngo
    wcel
    cG
    cgr
    wcel
    cX
    c0
    wne
    cR
    cG
    rngone0.1
    rngogrpo
    cG
    cX
    rngone0.2
    grpon0
    syl
end
