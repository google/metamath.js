include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cn.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "nnoddn2prm.mm"
include "simpl.mm"
include "3syl.mm"

theorem gausslemma2dlem0a
  let wph: wff ph
  let cP: class P
  assume gausslemma2dlem0a.p: |- ( ph -> P e. ( Prime \ { 2 } ) )


  assert |- ( ph -> P e. NN )

  proof
    wph
    cP
    cprime
    c2
    csn
    cdif
    wcel
    cP
    cn
    wcel
    #
    c2
    cP
    cdvds
    wbr
    wn
    #
    wa
    @0
    gausslemma2dlem0a.p
    cP
    nnoddn2prm
    @0
    @1
    simpl
    3syl
end
