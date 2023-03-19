include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "cicc.mm"
include "iccpartf.mm"
include "ffvelrnda.mm"

theorem iccpartel
  let wph: wff ph
  let cP: class P
  let cI: class I
  let cM: class M
  let vi: setvar i
  let vk: setvar k
  let vp: setvar p
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )


  assert |- ( ( ph /\ I e. ( 0 ... M ) ) -> ( P ` I ) e. ( ( P ` 0 ) [,] ( P ` M ) ) )

  proof
    wph
    cc0
    cM
    cfz
    co
    cc0
    cP
    cfv
    cM
    cP
    cfv
    cicc
    co
    cI
    cP
    wph
    cP
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartf
    ffvelrnda
end
