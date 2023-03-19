include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "simpl.mm"
include "cz.mm"
include "eluzelz.mm"
include "elfzuz3.mm"
include "peano2uzr.mm"
include "syl2an.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"

theorem peano2fzr
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ( ZZ>= ` M ) /\ ( K + 1 ) e. ( M ... N ) ) -> K e. ( M ... N ) )

  proof
    cK
    cM
    cuz
    cfv
    wcel
    #
    cK
    c1
    caddc
    co
    #
    cM
    cN
    cfz
    co
    #
    wcel
    #
    wa
    @0
    cN
    cK
    cuz
    cfv
    wcel
    #
    cK
    @2
    wcel
    @0
    @3
    simpl
    @0
    cK
    cz
    wcel
    cN
    @1
    cuz
    cfv
    wcel
    @4
    @3
    cM
    cK
    eluzelz
    @1
    cM
    cN
    elfzuz3
    cK
    cN
    peano2uzr
    syl2an
    cK
    cM
    cN
    elfzuzb
    sylanbrc
end
