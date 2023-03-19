include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "cn.mm"
include "c1.mm"
include "cmin.mm"
include "wi.mm"
include "wa.mm"
include "wlkdlem2.mm"
include "elfvdm.mm"
include "ralimi.mm"
include "adantl.mm"
include "syl.mm"
include "iswrdsymb.mm"
include "syl2anc.mm"

theorem wlkdlem3
  let wph: wff ph
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cI: class I
  assume wlkd.p: |- ( ph -> P e. Word _V )
  assume wlkd.f: |- ( ph -> F e. Word _V )
  assume wlkd.l: |- ( ph -> ( # ` P ) = ( ( # ` F ) + 1 ) )
  assume wlkd.e: |- ( ph -> A. k e. ( 0 ..^ ( # ` F ) ) { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) )

  disjoint F k
  disjoint P k
  disjoint I k
  disjoint k ph
  assert |- ( ph -> F e. Word dom I )

  proof
    wph
    cF
    cvv
    cword
    wcel
    vk
    cv
    #
    cF
    cfv
    #
    cI
    cdm
    #
    wcel
    #
    vk
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    cF
    @2
    cword
    wcel
    wlkd.f
    wph
    @4
    cn
    wcel
    @4
    cP
    cfv
    @4
    c1
    cmin
    co
    cF
    cfv
    cI
    cfv
    wcel
    wi
    #
    @0
    cP
    cfv
    #
    @1
    cI
    cfv
    wcel
    #
    vk
    @5
    wral
    #
    wa
    @6
    wph
    cP
    vk
    cF
    cI
    wlkd.p
    wlkd.f
    wlkd.l
    wlkd.e
    wlkdlem2
    @10
    @6
    @7
    @9
    @3
    vk
    @5
    @8
    @1
    cI
    elfvdm
    ralimi
    adantl
    syl
    vk
    @2
    cF
    iswrdsymb
    syl2anc
end
