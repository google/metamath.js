include "cv.mm"
include "cprod.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cid.mm"
include "cz.mm"
include "cres.mm"
include "cfv.mm"
include "wf1o.mm"
include "wf.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "fprodfvdvdsd.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "sselda.mm"
include "fvresi.mm"
include "syl.mm"
include "eqcomd.mm"
include "wi.mm"
include "sseld.mm"
include "adantr.mm"
include "imp.mm"
include "prodeq2dv.mm"
include "breq12d.mm"
include "ralbidva.mm"
include "mpbird.mm"

theorem fproddvdsd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  assume fproddvdsd.f: |- ( ph -> A e. Fin )
  assume fproddvdsd.s: |- ( ph -> A C_ ZZ )

  disjoint A k
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> A. x e. A x || prod_ k e. A k )

  proof
    wph
    vx
    cv
    #
    cA
    vk
    cv
    #
    vk
    cprod
    #
    cdvds
    wbr
    #
    vx
    cA
    wral
    @0
    cid
    cz
    cres
    #
    cfv
    #
    cA
    @1
    @4
    cfv
    #
    vk
    cprod
    #
    cdvds
    wbr
    #
    vx
    cA
    wral
    wph
    vx
    cA
    cz
    vk
    @4
    fproddvdsd.f
    fproddvdsd.s
    cz
    cz
    @4
    wf1o
    cz
    cz
    @4
    wf
    wph
    cz
    f1oi
    cz
    cz
    @4
    f1of
    mp1i
    fprodfvdvdsd
    wph
    @3
    @8
    vx
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @0
    @5
    @2
    @7
    cdvds
    @10
    @5
    @0
    @10
    @0
    cz
    wcel
    @5
    @0
    wceq
    wph
    cA
    cz
    @0
    fproddvdsd.s
    sselda
    cz
    @0
    fvresi
    syl
    eqcomd
    @10
    cA
    @1
    @6
    vk
    @10
    @1
    cA
    wcel
    #
    wa
    #
    @6
    @1
    @12
    @1
    cz
    wcel
    #
    @6
    @1
    wceq
    @10
    @11
    @13
    wph
    @11
    @13
    wi
    @9
    wph
    cA
    cz
    @1
    fproddvdsd.s
    sseld
    adantr
    imp
    cz
    @1
    fvresi
    syl
    eqcomd
    prodeq2dv
    breq12d
    ralbidva
    mpbird
end
