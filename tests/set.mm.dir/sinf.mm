include "cc.mm"
include "ci.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "df-sin.mm"
include "wcel.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "efcl.mm"
include "syl.mm"
include "negicn.mm"
include "subcld.mm"
include "cc0.mm"
include "wne.mm"
include "2mulicn.mm"
include "2muline0.mm"
include "divcl.mm"
include "mp3an23.mm"
include "fmpti.mm"

theorem sinf
  let vx: setvar x


  assert |- sin : CC --> CC

  proof
    vx
    cc
    cc
    ci
    vx
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    @0
    cmul
    co
    #
    ce
    cfv
    #
    cmin
    co
    #
    c2
    ci
    cmul
    co
    #
    cdiv
    co
    #
    csin
    vx
    df-sin
    @0
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    @9
    @2
    @5
    @9
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    ci
    cc
    wcel
    @9
    @12
    ax-icn
    ci
    @0
    mulcl
    mpan
    @1
    efcl
    syl
    @9
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    @3
    cc
    wcel
    @9
    @13
    negicn
    @3
    @0
    mulcl
    mpan
    @4
    efcl
    syl
    subcld
    @10
    @7
    cc
    wcel
    @7
    cc0
    wne
    @11
    2mulicn
    2muline0
    @6
    @7
    divcl
    mp3an23
    syl
    fmpti
end
