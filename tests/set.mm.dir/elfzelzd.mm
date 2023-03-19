include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "elfzelz.mm"
include "syl.mm"

theorem elfzelzd
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cN: class N
  assume elfzelzd.1: |- ( ph -> K e. ( M ... N ) )


  assert |- ( ph -> K e. ZZ )

  proof
    wph
    cK
    cM
    cN
    cfz
    co
    wcel
    cK
    cz
    wcel
    elfzelzd.1
    cK
    cM
    cN
    elfzelz
    syl
end
