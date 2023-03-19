include "cnzr.mm"
include "wcel.mm"
include "crg.mm"
include "wne.mm"
include "isnzr.mm"
include "simprbi.mm"

theorem nzrnz
  let cR: class R
  let c.1: class .1.
  let c.0: class .0.
  let vr: setvar r
  assume isnzr.o: |- .1. = ( 1r ` R )
  assume isnzr.z: |- .0. = ( 0g ` R )


  assert |- ( R e. NzRing -> .1. =/= .0. )

  proof
    cR
    cnzr
    wcel
    cR
    crg
    wcel
    c.1
    c.0
    wne
    cR
    c.1
    c.0
    isnzr.o
    isnzr.z
    isnzr
    simprbi
end
