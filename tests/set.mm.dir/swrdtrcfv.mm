include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "c0.mm"
include "wne.mm"
include "cfzo.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cn.mm"
include "lennncl.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "1nn0.mm"
include "a1i.mm"
include "nnnn0.mm"
include "nnge1.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "elfz1end.mm"
include "biimpi.mm"
include "jca.mm"
include "syl.mm"
include "3adant3.mm"
include "fz0fzdiffz0.mm"
include "swrd0fv.mm"
include "syld3an2.mm"

theorem swrdtrcfv
  let cI: class I
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ W =/= (/) /\ I e. ( 0 ..^ ( ( # ` W ) - 1 ) ) ) -> ( ( W substr <. 0 , ( ( # ` W ) - 1 ) >. ) ` I ) = ( W ` I ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cc0
    @1
    cfz
    co
    #
    wcel
    #
    cW
    c0
    wne
    #
    cI
    cc0
    @2
    cfzo
    co
    wcel
    #
    cI
    cW
    cc0
    @2
    cop
    csubstr
    co
    cfv
    cI
    cW
    cfv
    wceq
    @0
    @5
    @6
    w3a
    c1
    @3
    wcel
    #
    @1
    c1
    @1
    cfz
    co
    wcel
    #
    wa
    #
    @4
    @0
    @5
    @9
    @6
    @0
    @5
    wa
    @1
    cn
    wcel
    #
    @9
    cV
    cW
    lennncl
    @10
    @7
    @8
    @10
    c1
    cn0
    wcel
    #
    @1
    cn0
    wcel
    c1
    @1
    cle
    wbr
    @7
    @11
    @10
    1nn0
    a1i
    @1
    nnnn0
    @1
    nnge1
    c1
    @1
    elfz2nn0
    syl3anbrc
    @10
    @8
    @1
    elfz1end
    biimpi
    jca
    syl
    3adant3
    @1
    c1
    @1
    fz0fzdiffz0
    syl
    cI
    @2
    cV
    cW
    swrd0fv
    syld3an2
end
