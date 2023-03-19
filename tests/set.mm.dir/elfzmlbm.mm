include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cmin.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuz.mm"
include "uznn0sub.mm"
include "syl.mm"
include "elfzuz2.mm"
include "elfzelz.mm"
include "zred.mm"
include "elfzel2.mm"
include "elfzel1.mm"
include "elfzle2.mm"
include "lesub1dd.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"

theorem elfzmlbm
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> ( K - M ) e. ( 0 ... ( N - M ) ) )

  proof
    cK
    cM
    cN
    cfz
    co
    wcel
    #
    cK
    cM
    cmin
    co
    #
    cn0
    wcel
    #
    cN
    cM
    cmin
    co
    #
    cn0
    wcel
    #
    @1
    @3
    cle
    wbr
    @1
    cc0
    @3
    cfz
    co
    wcel
    @0
    cK
    cM
    cuz
    cfv
    #
    wcel
    @2
    cK
    cM
    cN
    elfzuz
    cM
    cK
    uznn0sub
    syl
    @0
    cN
    @5
    wcel
    @4
    cK
    cM
    cN
    elfzuz2
    cM
    cN
    uznn0sub
    syl
    @0
    cK
    cN
    cM
    @0
    cK
    cK
    cM
    cN
    elfzelz
    zred
    @0
    cN
    cK
    cM
    cN
    elfzel2
    zred
    @0
    cM
    cK
    cM
    cN
    elfzel1
    zred
    cK
    cM
    cN
    elfzle2
    lesub1dd
    @1
    @3
    elfz2nn0
    syl3anbrc
end
