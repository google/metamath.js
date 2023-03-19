include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "elfzle2.mm"
include "elfzle1.mm"
include "cz.mm"
include "wa.mm"
include "wb.mm"
include "elfzelz.mm"
include "elfzel2.mm"
include "cr.mm"
include "zre.mm"
include "letri3.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem elfz1eq
  let cK: class K
  let cN: class N


  assert |- ( K e. ( N ... N ) -> K = N )

  proof
    cK
    cN
    cN
    cfz
    co
    wcel
    #
    cK
    cN
    wceq
    #
    cK
    cN
    cle
    wbr
    #
    cN
    cK
    cle
    wbr
    #
    cK
    cN
    cN
    elfzle2
    cK
    cN
    cN
    elfzle1
    @0
    cK
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @1
    @2
    @3
    wa
    wb
    #
    cK
    cN
    cN
    elfzelz
    cK
    cN
    cN
    elfzel2
    @4
    cK
    cr
    wcel
    cN
    cr
    wcel
    @6
    @5
    cK
    zre
    cN
    zre
    cK
    cN
    letri3
    syl2an
    syl2anc
    mpbir2and
end
