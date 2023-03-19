include "cr.mm"
include "wcel.mm"
include "cn.mm"
include "cdiv.mm"
include "co.mm"
include "nndivre.mm"
include "syl2anc.mm"

theorem nndivred
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume nndivred.1: |- ( ph -> A e. RR )
  assume nndivred.2: |- ( ph -> B e. NN )


  assert |- ( ph -> ( A / B ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cB
    cn
    wcel
    cA
    cB
    cdiv
    co
    cr
    wcel
    nndivred.1
    nndivred.2
    cA
    cB
    nndivre
    syl2anc
end
