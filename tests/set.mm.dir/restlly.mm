include "clly.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ctop.mm"
include "wel.mm"
include "crest.mm"
include "co.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "sselda.mm"
include "simprl.mm"
include "vex.mm"
include "pwid.mm"
include "a1i.mm"
include "elind.mm"
include "simprr.mm"
include "anassrs.mm"
include "adantrr.mm"
include "weq.mm"
include "elequ2.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ralrimivva.mm"
include "islly.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem restlly
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cX: class X
  assume restlly.1: |- ( ( ph /\ ( j e. A /\ x e. j ) ) -> ( j |`t x ) e. A )
  assume restlly.2: |- ( ph -> A C_ Top )

  disjoint j x
  disjoint A j
  disjoint A x
  disjoint j ph
  disjoint ph x
  disjoint j k
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j y
  disjoint j z
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J j
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint k ph
  disjoint ph s
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint X u
  disjoint X y
  disjoint X z
  assert |- ( ph -> A C_ Locally A )

  proof
    wph
    vj
    cA
    cA
    clly
    #
    wph
    vj
    cv
    #
    cA
    wcel
    #
    @1
    @0
    wcel
    #
    wph
    @2
    wa
    #
    @1
    ctop
    wcel
    vy
    vu
    wel
    #
    @1
    vu
    cv
    #
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vu
    @1
    vx
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @10
    wral
    vx
    @1
    wral
    @3
    wph
    cA
    ctop
    @1
    restlly.2
    sselda
    @4
    @13
    vx
    vy
    @1
    @10
    @4
    vx
    vj
    wel
    #
    vy
    vx
    wel
    #
    wa
    wa
    #
    @10
    @12
    wcel
    @15
    @1
    @10
    crest
    co
    #
    cA
    wcel
    #
    @13
    @16
    @1
    @11
    @10
    @4
    @14
    @15
    simprl
    @10
    @11
    wcel
    @16
    @10
    vx
    vex
    pwid
    a1i
    elind
    @4
    @14
    @15
    simprr
    @4
    @14
    @18
    @15
    wph
    @2
    @14
    @18
    restlly.1
    anassrs
    adantrr
    @9
    @15
    @18
    wa
    vu
    @10
    @12
    vu
    vx
    weq
    #
    @5
    @15
    @8
    @18
    vu
    vx
    vy
    elequ2
    @19
    @7
    @17
    cA
    @6
    @10
    @1
    crest
    oveq2
    eleq1d
    anbi12d
    rspcev
    syl12anc
    ralrimivva
    vx
    vy
    vu
    cA
    @1
    islly
    sylanbrc
    ex
    ssrdv
end
