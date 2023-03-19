include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "eluzle.mm"
include "adantr.mm"
include "wi.mm"
include "eluzel2.mm"
include "eluzelz.mm"
include "jca.mm"
include "zletr.mm"
include "3expa.mm"
include "sylan.mm"
include "mpand.mm"
include "imdistanda.mm"
include "wb.mm"
include "eluz1.mm"
include "syl.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem uzss
  let cM: class M
  let cN: class N
  let vk: setvar k


  assert |- ( N e. ( ZZ>= ` M ) -> ( ZZ>= ` N ) C_ ( ZZ>= ` M ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    vk
    cN
    cuz
    cfv
    #
    @0
    @1
    vk
    cv
    #
    cz
    wcel
    #
    cN
    @3
    cle
    wbr
    #
    wa
    #
    @4
    cM
    @3
    cle
    wbr
    #
    wa
    #
    @3
    @2
    wcel
    #
    @3
    @0
    wcel
    #
    @1
    @4
    @5
    @7
    @1
    @4
    wa
    cM
    cN
    cle
    wbr
    #
    @5
    @7
    @1
    @11
    @4
    cM
    cN
    eluzle
    adantr
    @1
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    @4
    @11
    @5
    wa
    @7
    wi
    #
    @1
    @12
    @13
    cM
    cN
    eluzel2
    #
    cM
    cN
    eluzelz
    #
    jca
    @12
    @13
    @4
    @14
    cM
    cN
    @3
    zletr
    3expa
    sylan
    mpand
    imdistanda
    @1
    @13
    @9
    @6
    wb
    @16
    cN
    @3
    eluz1
    syl
    @1
    @12
    @10
    @8
    wb
    @15
    cM
    @3
    eluz1
    syl
    3imtr4d
    ssrdv
end
