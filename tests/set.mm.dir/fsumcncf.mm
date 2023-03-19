include "csu.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "cc.mm"
include "ccncf.mm"
include "eqid.mm"
include "ctopon.mm"
include "wcel.mm"
include "wss.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "resttopon.mm"
include "syl2anc.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "ssid.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "unicntop.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "fsumcnf.mm"
include "eleqtrrd.mm"

theorem fsumcncf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cX: class X
  assume fsumcncf.x: |- ( ph -> X C_ CC )
  assume fsumcncf.a: |- ( ph -> A e. Fin )
  assume fsumcncf.cncf: |- ( ( ph /\ k e. A ) -> ( x e. X |-> B ) e. ( X -cn-> CC ) )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint X k
  disjoint X x
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ( x e. X |-> sum_ k e. A B ) e. ( X -cn-> CC ) )

  proof
    wph
    vx
    cX
    cA
    cB
    vk
    csu
    cmpt
    ccnfld
    ctopn
    cfv
    #
    cX
    crest
    co
    #
    @0
    ccn
    co
    #
    cX
    cc
    ccncf
    co
    #
    wph
    vx
    cA
    cB
    vk
    @1
    @0
    cX
    @0
    eqid
    #
    wph
    @0
    cc
    ctopon
    cfv
    wcel
    #
    cX
    cc
    wss
    #
    @1
    cX
    ctopon
    cfv
    wcel
    @5
    wph
    @0
    @4
    cnfldtopon
    a1i
    fsumcncf.x
    cX
    @0
    cc
    resttopon
    syl2anc
    fsumcncf.a
    wph
    vk
    cv
    cA
    wcel
    #
    wa
    vx
    cX
    cB
    cmpt
    @3
    @2
    fsumcncf.cncf
    wph
    @3
    @2
    wceq
    #
    @7
    wph
    @6
    cc
    cc
    wss
    #
    @8
    fsumcncf.x
    @9
    wph
    cc
    ssid
    a1i
    cX
    cc
    @0
    @1
    @0
    @4
    @1
    eqid
    @0
    cc
    crest
    co
    #
    @0
    @0
    ctop
    wcel
    @10
    @0
    wceq
    @0
    @4
    cnfldtop
    @0
    ctop
    cc
    unicntop
    restid
    ax-mp
    eqcomi
    cncfcn
    syl2anc
    #
    adantr
    eleqtrd
    fsumcnf
    @11
    eleqtrrd
end
