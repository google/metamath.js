include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "cfv.mm"
include "iccssxr.mm"
include "omecl.mm"
include "sseldi.mm"

theorem omexrcl
  let wph: wff ph
  let cA: class A
  let cO: class O
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume omexrcl.o: |- ( ph -> O e. OutMeas )
  assume omexrcl.x: |- X = U. dom O
  assume omexrcl.a: |- ( ph -> A C_ X )


  assert |- ( ph -> ( O ` A ) e. RR* )

  proof
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    cA
    cO
    cfv
    cc0
    cpnf
    iccssxr
    wph
    cA
    cO
    cX
    omexrcl.o
    omexrcl.x
    omexrcl.a
    omecl
    sseldi
end
