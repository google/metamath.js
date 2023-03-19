include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cle.mm"
include "wbr.mm"
include "eluzle.mm"
include "clt.mm"
include "wn.mm"
include "cz.mm"
include "eluzel2.mm"
include "wi.mm"
include "elfzel1.mm"
include "wa.mm"
include "w3a.mm"
include "elfzm11.mm"
include "simp3.mm"
include "syl6bi.mm"
include "impancom.mm"
include "mpancom.mm"
include "syl5com.mm"
include "wb.mm"
include "eluzelz.mm"
include "cr.mm"
include "zre.mm"
include "ltnle.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "mt2d.mm"

theorem uznfz
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( ZZ>= ` N ) -> -. K e. ( M ... ( N - 1 ) ) )

  proof
    cK
    cN
    cuz
    cfv
    wcel
    #
    cK
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    cN
    cK
    cle
    wbr
    #
    cN
    cK
    eluzle
    @0
    @2
    cK
    cN
    clt
    wbr
    #
    @3
    wn
    #
    @0
    cN
    cz
    wcel
    #
    @2
    @4
    cN
    cK
    eluzel2
    #
    cM
    cz
    wcel
    #
    @2
    @6
    @4
    wi
    cK
    cM
    @1
    elfzel1
    @8
    @6
    @2
    @4
    @8
    @6
    wa
    @2
    cK
    cz
    wcel
    #
    cM
    cK
    cle
    wbr
    #
    @4
    w3a
    @4
    cK
    cM
    cN
    elfzm11
    @9
    @10
    @4
    simp3
    syl6bi
    impancom
    mpancom
    syl5com
    @0
    @9
    @6
    @4
    @5
    wb
    #
    cN
    cK
    eluzelz
    @7
    @9
    cK
    cr
    wcel
    cN
    cr
    wcel
    @11
    @6
    cK
    zre
    cN
    zre
    cK
    cN
    ltnle
    syl2an
    syl2anc
    sylibd
    mt2d
end
