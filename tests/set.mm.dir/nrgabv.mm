include "cnrg.mm"
include "wcel.mm"
include "cngp.mm"
include "isnrg.mm"
include "simprbi.mm"

theorem nrgabv
  let cA: class A
  let cR: class R
  let cN: class N
  let vr: setvar r
  assume isnrg.1: |- N = ( norm ` R )
  assume isnrg.2: |- A = ( AbsVal ` R )


  assert |- ( R e. NrmRing -> N e. A )

  proof
    cR
    cnrg
    wcel
    cR
    cngp
    wcel
    cN
    cA
    wcel
    cA
    cR
    cN
    isnrg.1
    isnrg.2
    isnrg
    simprbi
end
