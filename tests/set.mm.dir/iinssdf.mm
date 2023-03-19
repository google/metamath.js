include "wss.mm"
include "wrex.mm"
include "ciin.mm"
include "wcel.mm"
include "nfss.mm"
include "cv.mm"
include "wceq.mm"
include "sseq1d.mm"
include "rspcef.mm"
include "syl2anc.mm"
include "iinssf.mm"
include "syl.mm"

theorem iinssdf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  assume iinssdf.a: |- F/_ x A
  assume iinssdf.n: |- F/_ x X
  assume iinssdf.c: |- F/_ x C
  assume iinssdf.d: |- F/_ x D
  assume iinssdf.x: |- ( ph -> X e. A )
  assume iinssdf.b: |- ( x = X -> B = D )
  assume iinssdf.s: |- ( ph -> D C_ C )


  assert |- ( ph -> |^|_ x e. A B C_ C )

  proof
    wph
    cB
    cC
    wss
    #
    vx
    cA
    wrex
    #
    vx
    cA
    cB
    ciin
    cC
    wss
    wph
    cX
    cA
    wcel
    cD
    cC
    wss
    #
    @1
    iinssdf.x
    iinssdf.s
    @0
    @2
    vx
    cX
    cA
    vx
    cD
    cC
    iinssdf.d
    iinssdf.c
    nfss
    iinssdf.n
    iinssdf.a
    vx
    cv
    cX
    wceq
    cB
    cD
    cC
    iinssdf.b
    sseq1d
    rspcef
    syl2anc
    vx
    cA
    cB
    cC
    iinssdf.c
    iinssf
    syl
end
