include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "3jca.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"

theorem elfzd
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cN: class N
  assume elfzd.1: |- ( ph -> M e. ZZ )
  assume elfzd.2: |- ( ph -> N e. ZZ )
  assume elfzd.3: |- ( ph -> K e. ZZ )
  assume elfzd.4: |- ( ph -> M <_ K )
  assume elfzd.5: |- ( ph -> K <_ N )


  assert |- ( ph -> K e. ( M ... N ) )

  proof
    wph
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    w3a
    #
    cM
    cK
    cle
    wbr
    #
    cK
    cN
    cle
    wbr
    #
    wa
    wa
    cK
    cM
    cN
    cfz
    co
    wcel
    wph
    @3
    @4
    @5
    wph
    @0
    @1
    @2
    elfzd.1
    elfzd.2
    elfzd.3
    3jca
    elfzd.4
    elfzd.5
    jca32
    cK
    cM
    cN
    elfz2
    sylibr
end
