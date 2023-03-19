include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "cexp.mm"
include "cmin.mm"
include "c8.mm"
include "cdiv.mm"
include "odd2np1.mm"
include "biimpa.mm"
include "eqcom.mm"
include "sqoddm1div8.mm"
include "adantll.mm"
include "mulsucdiv2z.mm"
include "ad2antlr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "syl5bi.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem sqoddm1div8z
  let cN: class N
  let vk: setvar k


  assert |- ( ( N e. ZZ /\ -. 2 || N ) -> ( ( ( N ^ 2 ) - 1 ) / 8 ) e. ZZ )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    wa
    #
    c2
    vk
    cv
    #
    cmul
    co
    c1
    caddc
    co
    #
    cN
    wceq
    #
    vk
    cz
    wrex
    #
    cN
    c2
    cexp
    co
    c1
    cmin
    co
    c8
    cdiv
    co
    #
    cz
    wcel
    #
    @0
    @1
    @6
    vk
    cN
    odd2np1
    biimpa
    @2
    @5
    @8
    vk
    cz
    @5
    cN
    @4
    wceq
    #
    @2
    @3
    cz
    wcel
    #
    wa
    #
    @8
    @4
    cN
    eqcom
    @11
    @9
    @8
    @11
    @9
    wa
    @7
    @3
    @3
    c1
    caddc
    co
    cmul
    co
    c2
    cdiv
    co
    #
    cz
    @10
    @9
    @7
    @12
    wceq
    @2
    cN
    @3
    sqoddm1div8
    adantll
    @10
    @12
    cz
    wcel
    @2
    @9
    @3
    mulsucdiv2z
    ad2antlr
    eqeltrd
    ex
    syl5bi
    rexlimdva
    mpd
end
