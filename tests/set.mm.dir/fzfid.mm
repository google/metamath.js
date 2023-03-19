include "cfz.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "fzfi.mm"
include "a1i.mm"

theorem fzfid
  let wph: wff ph
  let cM: class M
  let cN: class N


  assert |- ( ph -> ( M ... N ) e. Fin )

  proof
    cM
    cN
    cfz
    co
    cfn
    wcel
    wph
    cM
    cN
    fzfi
    a1i
end
