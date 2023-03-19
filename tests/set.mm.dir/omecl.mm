include "cpw.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "omef.mm"
include "wcel.mm"
include "wss.mm"
include "cvv.mm"
include "wb.mm"
include "cdm.mm"
include "cuni.mm"
include "wceq.mm"
include "a1i.mm"
include "come.mm"
include "dmexg.mm"
include "syl.mm"
include "uniexg.mm"
include "eqeltrd.mm"
include "ssexd.mm"
include "elpwg.mm"
include "mpbird.mm"
include "ffvelrnd.mm"

theorem omecl
  let wph: wff ph
  let cA: class A
  let cO: class O
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume omecl.o: |- ( ph -> O e. OutMeas )
  assume omecl.x: |- X = U. dom O
  assume omecl.ss: |- ( ph -> A C_ X )


  assert |- ( ph -> ( O ` A ) e. ( 0 [,] +oo ) )

  proof
    wph
    cX
    cpw
    #
    cc0
    cpnf
    cicc
    co
    cA
    cO
    wph
    cO
    cX
    omecl.o
    omecl.x
    omef
    wph
    cA
    @0
    wcel
    #
    cA
    cX
    wss
    #
    omecl.ss
    wph
    cA
    cvv
    wcel
    @1
    @2
    wb
    wph
    cA
    cX
    cvv
    wph
    cX
    cO
    cdm
    #
    cuni
    #
    cvv
    cX
    @4
    wceq
    wph
    omecl.x
    a1i
    wph
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    wph
    cO
    come
    wcel
    @5
    omecl.o
    cO
    come
    dmexg
    syl
    @3
    cvv
    uniexg
    syl
    eqeltrd
    omecl.ss
    ssexd
    cA
    cX
    cvv
    elpwg
    syl
    mpbird
    ffvelrnd
end
