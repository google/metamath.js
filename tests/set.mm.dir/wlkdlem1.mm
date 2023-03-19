include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cvv.mm"
include "wf.mm"
include "cfz.mm"
include "cword.mm"
include "wcel.mm"
include "wrdf.mm"
include "syl.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2d.mm"
include "cz.mm"
include "wceq.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzval3.mm"
include "eqtr4d.mm"
include "feq2d.mm"
include "wss.mm"
include "cv.mm"
include "wral.mm"
include "wb.mm"
include "ssv.mm"
include "frnssb.mm"
include "sylancr.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem wlkdlem1
  let wph: wff ph
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cV: class V
  assume wlkd.p: |- ( ph -> P e. Word _V )
  assume wlkd.f: |- ( ph -> F e. Word _V )
  assume wlkd.l: |- ( ph -> ( # ` P ) = ( ( # ` F ) + 1 ) )
  assume wlkdlem1.v: |- ( ph -> A. k e. ( 0 ... ( # ` F ) ) ( P ` k ) e. V )

  disjoint V k
  disjoint F k
  disjoint P k
  assert |- ( ph -> P : ( 0 ... ( # ` F ) ) --> V )

  proof
    wph
    cc0
    cP
    chash
    cfv
    #
    cfzo
    co
    #
    cvv
    cP
    wf
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf
    #
    wph
    cP
    cvv
    cword
    #
    wcel
    @2
    wlkd.p
    cvv
    cP
    wrdf
    syl
    wph
    @2
    @4
    cvv
    cP
    wf
    #
    @5
    wph
    @1
    @4
    cvv
    cP
    wph
    @1
    cc0
    @3
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @4
    wph
    @0
    @8
    cc0
    cfzo
    wlkd.l
    oveq2d
    wph
    @3
    cz
    wcel
    @4
    @9
    wceq
    wph
    @3
    wph
    cF
    @6
    wcel
    @3
    cn0
    wcel
    wlkd.f
    cvv
    cF
    lencl
    syl
    nn0zd
    cc0
    @3
    fzval3
    syl
    eqtr4d
    feq2d
    wph
    cV
    cvv
    wss
    vk
    cv
    cP
    cfv
    cV
    wcel
    vk
    @4
    wral
    @7
    @5
    wb
    cV
    ssv
    wlkdlem1.v
    @4
    vk
    cP
    cV
    cvv
    frnssb
    sylancr
    bitrd
    mpbid
end
