include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "covoln.mm"
include "cfv.mm"
include "ovnf.mm"
include "wcel.mm"
include "wss.mm"
include "cvv.mm"
include "wb.mm"
include "ovexd.mm"
include "ssexd.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "ffvelrnd.mm"

theorem ovncl
  let wph: wff ph
  let cA: class A
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume ovncl.1: |- ( ph -> X e. Fin )
  assume ovncl.2: |- ( ph -> A C_ ( RR ^m X ) )


  assert |- ( ph -> ( ( voln* ` X ) ` A ) e. ( 0 [,] +oo ) )

  proof
    wph
    cr
    cX
    cmap
    co
    #
    cpw
    #
    cc0
    cpnf
    cicc
    co
    cA
    cX
    covoln
    cfv
    wph
    cX
    ovncl.1
    ovnf
    wph
    cA
    @1
    wcel
    #
    cA
    @0
    wss
    #
    ovncl.2
    wph
    cA
    cvv
    wcel
    @2
    @3
    wb
    wph
    cA
    @0
    cvv
    wph
    cr
    cX
    cmap
    ovexd
    ovncl.2
    ssexd
    cA
    @0
    cvv
    elpwg
    syl
    mpbird
    ffvelrnd
end
