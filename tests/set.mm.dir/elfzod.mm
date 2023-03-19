include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "co.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"

theorem elfzod
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cN: class N
  assume elfzod.1: |- ( ph -> K e. ( ZZ>= ` M ) )
  assume elfzod.2: |- ( ph -> N e. ZZ )
  assume elfzod.3: |- ( ph -> K < N )


  assert |- ( ph -> K e. ( M ..^ N ) )

  proof
    wph
    cK
    cM
    cuz
    cfv
    wcel
    cN
    cz
    wcel
    cK
    cN
    clt
    wbr
    cK
    cM
    cN
    cfzo
    co
    wcel
    elfzod.1
    elfzod.2
    elfzod.3
    cK
    cM
    cN
    elfzo2
    syl3anbrc
end
