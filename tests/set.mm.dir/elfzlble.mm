include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cfz.mm"
include "cle.mm"
include "wbr.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "sylan2.mm"
include "simpl.mm"
include "cc0.mm"
include "nn0ge0.mm"
include "adantl.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "nn0re.mm"
include "subge02.mm"
include "syl2an.mm"
include "mpbid.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "eluzfz2.mm"
include "syl.mm"

theorem elfzlble
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. ZZ /\ M e. NN0 ) -> N e. ( ( N - M ) ... N ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    cN
    cN
    cM
    cmin
    co
    #
    cuz
    cfv
    wcel
    #
    cN
    @3
    cN
    cfz
    co
    wcel
    @2
    @3
    cz
    wcel
    #
    @0
    @3
    cN
    cle
    wbr
    #
    @4
    @1
    @0
    cM
    cz
    wcel
    @5
    cM
    nn0z
    cN
    cM
    zsubcl
    sylan2
    @0
    @1
    simpl
    @2
    cc0
    cM
    cle
    wbr
    #
    @6
    @1
    @7
    @0
    cM
    nn0ge0
    adantl
    @0
    cN
    cr
    wcel
    cM
    cr
    wcel
    @7
    @6
    wb
    @1
    cN
    zre
    cM
    nn0re
    cN
    cM
    subge02
    syl2an
    mpbid
    @3
    cN
    eluz2
    syl3anbrc
    @3
    cN
    eluzfz2
    syl
end
