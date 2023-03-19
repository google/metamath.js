include "cfv.mm"
include "cc0.mm"
include "sstrd.mm"
include "omexrcl.mm"
include "cxr.mm"
include "wcel.mm"
include "0xr.mm"
include "a1i.mm"
include "cle.mm"
include "omessle.mm"
include "breqtrd.mm"
include "omege0.mm"
include "xrletrid.mm"

theorem omess0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cO: class O
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume omess0.o: |- ( ph -> O e. OutMeas )
  assume omess0.x: |- X = U. dom O
  assume omess0.a: |- ( ph -> A C_ X )
  assume omess0.z: |- ( ph -> ( O ` A ) = 0 )
  assume omess0.s: |- ( ph -> B C_ A )


  assert |- ( ph -> ( O ` B ) = 0 )

  proof
    wph
    cB
    cO
    cfv
    #
    cc0
    wph
    cB
    cO
    cX
    omess0.o
    omess0.x
    wph
    cB
    cA
    cX
    omess0.s
    omess0.a
    sstrd
    #
    omexrcl
    cc0
    cxr
    wcel
    wph
    0xr
    a1i
    wph
    @0
    cA
    cO
    cfv
    cc0
    cle
    wph
    cB
    cA
    cO
    cX
    omess0.o
    omess0.x
    omess0.a
    omess0.s
    omessle
    omess0.z
    breqtrd
    wph
    cB
    cO
    cX
    omess0.o
    omess0.x
    @1
    omege0
    xrletrid
end
