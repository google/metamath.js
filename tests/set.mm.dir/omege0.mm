include "cc0.mm"
include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "omecl.mm"
include "iccgelb.mm"
include "syl3anc.mm"

theorem omege0
  let wph: wff ph
  let cA: class A
  let cO: class O
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume omege0.o: |- ( ph -> O e. OutMeas )
  assume omege0.x: |- X = U. dom O
  assume omege0.a: |- ( ph -> A C_ X )


  assert |- ( ph -> 0 <_ ( O ` A ) )

  proof
    wph
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cA
    cO
    cfv
    #
    cc0
    cpnf
    cicc
    co
    wcel
    cc0
    @2
    cle
    wbr
    @0
    wph
    0xr
    a1i
    @1
    wph
    pnfxr
    a1i
    wph
    cA
    cO
    cX
    omege0.o
    omege0.x
    omege0.a
    omecl
    cc0
    cpnf
    @2
    iccgelb
    syl3anc
end
