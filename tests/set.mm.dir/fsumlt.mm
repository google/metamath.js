include "csu.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "cr.mm"
include "wb.mm"
include "difrp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "fsumrpcl.mm"
include "rpgt0d.mm"
include "recnd.mm"
include "fsumsub.mm"
include "breqtrd.mm"
include "fsumrecl.mm"
include "posdifd.mm"
include "mpbird.mm"

theorem fsumlt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume fsumlt.1: |- ( ph -> A e. Fin )
  assume fsumlt.2: |- ( ph -> A =/= (/) )
  assume fsumlt.3: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume fsumlt.4: |- ( ( ph /\ k e. A ) -> C e. RR )
  assume fsumlt.5: |- ( ( ph /\ k e. A ) -> B < C )

  disjoint A k
  disjoint k ph
  assert |- ( ph -> sum_ k e. A B < sum_ k e. A C )

  proof
    wph
    cA
    cB
    vk
    csu
    #
    cA
    cC
    vk
    csu
    #
    clt
    wbr
    cc0
    @1
    @0
    cmin
    co
    #
    clt
    wbr
    wph
    cc0
    cA
    cC
    cB
    cmin
    co
    #
    vk
    csu
    #
    @2
    clt
    wph
    @4
    wph
    cA
    @3
    vk
    fsumlt.1
    fsumlt.2
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    cB
    cC
    clt
    wbr
    #
    @3
    crp
    wcel
    #
    fsumlt.5
    @5
    cB
    cr
    wcel
    cC
    cr
    wcel
    @6
    @7
    wb
    fsumlt.3
    fsumlt.4
    cB
    cC
    difrp
    syl2anc
    mpbid
    fsumrpcl
    rpgt0d
    wph
    cA
    cC
    cB
    vk
    fsumlt.1
    @5
    cC
    fsumlt.4
    recnd
    @5
    cB
    fsumlt.3
    recnd
    fsumsub
    breqtrd
    wph
    @0
    @1
    wph
    cA
    cB
    vk
    fsumlt.1
    fsumlt.3
    fsumrecl
    wph
    cA
    cC
    vk
    fsumlt.1
    fsumlt.4
    fsumrecl
    posdifd
    mpbird
end
