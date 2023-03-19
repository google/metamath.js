include "cz.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "cmin.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "elfzoel2.mm"
include "zsubcl.mm"
include "ex.mm"
include "syl.mm"
include "impcom.mm"
include "3adant2.mm"
include "adantr.mm"
include "simp3.mm"
include "anim1i.mm"
include "elfzonelfzo.mm"
include "sylc.mm"
include "con1d.mm"

theorem fzonfzoufzol
  let cI: class I
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ M < N /\ I e. ( 0 ..^ N ) ) -> ( -. I e. ( ( N - M ) ..^ N ) -> I e. ( 0 ..^ ( N - M ) ) ) )

  proof
    cM
    cz
    wcel
    #
    cM
    cN
    clt
    wbr
    #
    cI
    cc0
    cN
    cfzo
    co
    wcel
    #
    w3a
    #
    cI
    cc0
    cN
    cM
    cmin
    co
    #
    cfzo
    co
    wcel
    #
    cI
    @4
    cN
    cfzo
    co
    wcel
    #
    @3
    @5
    wn
    #
    @6
    @3
    @7
    wa
    @4
    cz
    wcel
    #
    @2
    @7
    wa
    @6
    @3
    @8
    @7
    @0
    @2
    @8
    @1
    @2
    @0
    @8
    @2
    cN
    cz
    wcel
    #
    @0
    @8
    wi
    cI
    cc0
    cN
    elfzoel2
    @9
    @0
    @8
    cN
    cM
    zsubcl
    ex
    syl
    impcom
    3adant2
    adantr
    @3
    @2
    @7
    @0
    @1
    @2
    simp3
    anim1i
    cN
    cI
    cc0
    @4
    elfzonelfzo
    sylc
    ex
    con1d
end
