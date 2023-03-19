include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "imp.mm"
include "an32.mm"
include "anbi2i.mm"
include "anass.mm"
include "bitr4i.mm"
include "sylbir.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimivva.mm"
include "jca.mm"
include "elcncf.mm"
include "syl5ibrcom.mm"

theorem elcncf1di
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  let cZ: class Z
  let vz: setvar z
  assume elcncf1d.1: |- ( ph -> F : A --> B )
  assume elcncf1d.2: |- ( ph -> ( ( x e. A /\ y e. RR+ ) -> Z e. RR+ ) )
  assume elcncf1d.3: |- ( ph -> ( ( ( x e. A /\ w e. A ) /\ y e. RR+ ) -> ( ( abs ` ( x - w ) ) < Z -> ( abs ` ( ( F ` x ) - ( F ` w ) ) ) < y ) ) )

  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint Z w
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint F z
  disjoint Z z
  assert |- ( ph -> ( ( A C_ CC /\ B C_ CC ) -> F e. ( A -cn-> B ) ) )

  proof
    wph
    cF
    cA
    cB
    ccncf
    co
    wcel
    cA
    cc
    wss
    cB
    cc
    wss
    wa
    cA
    cB
    cF
    wf
    #
    vx
    cv
    #
    vw
    cv
    #
    cmin
    co
    cabs
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @1
    cF
    cfv
    @2
    cF
    cfv
    cmin
    co
    cabs
    cfv
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    cA
    wral
    #
    wa
    wph
    @0
    @11
    elcncf1d.1
    wph
    @10
    vx
    vy
    cA
    crp
    wph
    @1
    cA
    wcel
    #
    @6
    crp
    wcel
    #
    wa
    #
    wa
    #
    cZ
    crp
    wcel
    #
    @3
    cZ
    clt
    wbr
    #
    @7
    wi
    #
    vw
    cA
    wral
    #
    @10
    wph
    @14
    @16
    elcncf1d.2
    imp
    @15
    @18
    vw
    cA
    @15
    @2
    cA
    wcel
    #
    wa
    #
    wph
    @12
    @20
    wa
    @13
    wa
    #
    wa
    #
    @18
    @23
    wph
    @14
    @20
    wa
    #
    wa
    @21
    @22
    @24
    wph
    @12
    @20
    @13
    an32
    anbi2i
    wph
    @14
    @20
    anass
    bitr4i
    wph
    @22
    @18
    elcncf1d.3
    imp
    sylbir
    ralrimiva
    @9
    @19
    vz
    cZ
    crp
    @4
    cZ
    wceq
    #
    @8
    @18
    vw
    cA
    @25
    @5
    @17
    @7
    @4
    cZ
    @3
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimivva
    jca
    vx
    vy
    vz
    vw
    cA
    cB
    cF
    elcncf
    syl5ibrcom
end
