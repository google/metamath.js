include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "elfzle1.mm"
include "cz.mm"
include "wb.mm"
include "elfzel2.mm"
include "elfzelz.mm"
include "cr.mm"
include "zre.mm"
include "subge02.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cuz.mm"
include "cfv.mm"
include "cn0.mm"
include "fznn0sub.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "elfz5.mm"
include "mpbird.mm"

theorem fznn0sub2
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 0 ... N ) -> ( N - K ) e. ( 0 ... N ) )

  proof
    cK
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cN
    cK
    cmin
    co
    #
    @0
    wcel
    #
    @2
    cN
    cle
    wbr
    #
    @1
    cc0
    cK
    cle
    wbr
    #
    @4
    cK
    cc0
    cN
    elfzle1
    @1
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @5
    @4
    wb
    #
    cK
    cc0
    cN
    elfzel2
    #
    cK
    cc0
    cN
    elfzelz
    @6
    cN
    cr
    wcel
    cK
    cr
    wcel
    @8
    @7
    cN
    zre
    cK
    zre
    cN
    cK
    subge02
    syl2an
    syl2anc
    mpbid
    @1
    @2
    cc0
    cuz
    cfv
    #
    wcel
    @6
    @3
    @4
    wb
    @1
    @2
    cn0
    @10
    cK
    cc0
    cN
    fznn0sub
    nn0uz
    syl6eleq
    @9
    @2
    cc0
    cN
    elfz5
    syl2anc
    mpbird
end
