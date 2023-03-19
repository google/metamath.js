include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "elfzle2.mm"
include "clt.mm"
include "wn.mm"
include "cz.mm"
include "wi.mm"
include "elfzel2.mm"
include "eluzp1l.mm"
include "ex.mm"
include "syl.mm"
include "wb.mm"
include "elfzelz.mm"
include "cr.mm"
include "zre.mm"
include "ltnle.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "mt2d.mm"

theorem fznuz
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> -. K e. ( ZZ>= ` ( N + 1 ) ) )

  proof
    cK
    cM
    cN
    cfz
    co
    wcel
    #
    cK
    cN
    c1
    caddc
    co
    cuz
    cfv
    wcel
    #
    cK
    cN
    cle
    wbr
    #
    cK
    cM
    cN
    elfzle2
    @0
    @1
    cN
    cK
    clt
    wbr
    #
    @2
    wn
    #
    @0
    cN
    cz
    wcel
    #
    @1
    @3
    wi
    cK
    cM
    cN
    elfzel2
    #
    @5
    @1
    @3
    cN
    cK
    eluzp1l
    ex
    syl
    @0
    @5
    cK
    cz
    wcel
    #
    @3
    @4
    wb
    #
    @6
    cK
    cM
    cN
    elfzelz
    @5
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
    ltnle
    syl2an
    syl2anc
    sylibd
    mt2d
end
