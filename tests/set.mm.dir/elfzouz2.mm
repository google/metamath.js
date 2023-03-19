include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzoelz.mm"
include "elfzoel2.mm"
include "clt.mm"
include "elfzolt2.mm"
include "wi.mm"
include "cr.mm"
include "zre.mm"
include "ltle.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "mpd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"

theorem elfzouz2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> N e. ( ZZ>= ` K ) )

  proof
    cK
    cM
    cN
    cfzo
    co
    wcel
    #
    cK
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cN
    cle
    wbr
    #
    cN
    cK
    cuz
    cfv
    wcel
    cK
    cM
    cN
    elfzoelz
    #
    cK
    cM
    cN
    elfzoel2
    #
    @0
    cK
    cN
    clt
    wbr
    #
    @3
    cK
    cM
    cN
    elfzolt2
    @0
    @1
    @2
    @6
    @3
    wi
    #
    @4
    @5
    @1
    cK
    cr
    wcel
    cN
    cr
    wcel
    @7
    @2
    cK
    zre
    cN
    zre
    cK
    cN
    ltle
    syl2an
    syl2anc
    mpd
    cK
    cN
    eluz2
    syl3anbrc
end
