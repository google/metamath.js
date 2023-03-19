include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "elfzuzb.mm"
include "eqid.mm"
include "uztrn2.mm"
include "sylbi.mm"

theorem elfzuz2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> N e. ( ZZ>= ` M ) )

  proof
    cK
    cM
    cN
    cfz
    co
    wcel
    cK
    cM
    cuz
    cfv
    #
    wcel
    cN
    cK
    cuz
    cfv
    wcel
    wa
    cN
    @0
    wcel
    cK
    cM
    cN
    elfzuzb
    cM
    cN
    cK
    @0
    @0
    eqid
    uztrn2
    sylbi
end
