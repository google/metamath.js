include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "w3a.mm"
include "cbs.mm"
include "wral.mm"
include "cpo.mm"
include "adantrr.mm"
include "adantr.mm"
include "3expb.mm"
include "3exp2.mm"
include "imp42.mm"
include "3jca.mm"
include "ralrimiva.mm"
include "ralrimivva.mm"
include "breqd.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "imbi12d.mm"
include "3anbi123d.mm"
include "raleqbidv.mm"
include "anbi2d.mm"
include "mpbi2and.mm"
include "eqid.mm"
include "ispos.mm"
include "sylibr.mm"

theorem isposd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  assume isposd.k: |- ( ph -> K e. _V )
  assume isposd.b: |- ( ph -> B = ( Base ` K ) )
  assume isposd.l: |- ( ph -> .<_ = ( le ` K ) )
  assume isposd.1: |- ( ( ph /\ x e. B ) -> x .<_ x )
  assume isposd.2: |- ( ( ph /\ x e. B /\ y e. B ) -> ( ( x .<_ y /\ y .<_ x ) -> x = y ) )
  assume isposd.3: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> K e. Poset )

  proof
    wph
    cK
    cvv
    wcel
    #
    vx
    cv
    #
    @1
    cK
    cple
    cfv
    #
    wbr
    #
    @1
    vy
    cv
    #
    @2
    wbr
    #
    @4
    @1
    @2
    wbr
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    @5
    @4
    vz
    cv
    #
    @2
    wbr
    #
    wa
    #
    @1
    @10
    @2
    wbr
    #
    wi
    #
    w3a
    #
    vz
    cK
    cbs
    cfv
    #
    wral
    #
    vy
    @16
    wral
    #
    vx
    @16
    wral
    #
    wa
    #
    cK
    cpo
    wcel
    wph
    @0
    @1
    @1
    c.le
    wbr
    #
    @1
    @4
    c.le
    wbr
    #
    @4
    @1
    c.le
    wbr
    #
    wa
    #
    @8
    wi
    #
    @22
    @4
    @10
    c.le
    wbr
    #
    wa
    #
    @1
    @10
    c.le
    wbr
    #
    wi
    #
    w3a
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @20
    isposd.k
    wph
    @31
    vx
    vy
    cB
    cB
    wph
    @1
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    wa
    #
    @30
    vz
    cB
    @36
    @10
    cB
    wcel
    #
    wa
    @21
    @25
    @29
    @36
    @21
    @37
    wph
    @34
    @21
    @35
    isposd.1
    adantrr
    adantr
    @36
    @25
    @37
    wph
    @34
    @35
    @25
    isposd.2
    3expb
    adantr
    wph
    @34
    @35
    @37
    @29
    wph
    @34
    @35
    @37
    @29
    isposd.3
    3exp2
    imp42
    3jca
    ralrimiva
    ralrimivva
    wph
    @33
    @19
    @0
    wph
    @32
    @18
    vx
    cB
    @16
    isposd.b
    wph
    @31
    @17
    vy
    cB
    @16
    isposd.b
    wph
    @30
    @15
    vz
    cB
    @16
    isposd.b
    wph
    @21
    @3
    @25
    @9
    @29
    @14
    wph
    c.le
    @2
    @1
    @1
    isposd.l
    breqd
    wph
    @24
    @7
    @8
    wph
    @22
    @5
    @23
    @6
    wph
    c.le
    @2
    @1
    @4
    isposd.l
    breqd
    #
    wph
    c.le
    @2
    @4
    @1
    isposd.l
    breqd
    anbi12d
    imbi1d
    wph
    @27
    @12
    @28
    @13
    wph
    @22
    @5
    @26
    @11
    @38
    wph
    c.le
    @2
    @4
    @10
    isposd.l
    breqd
    anbi12d
    wph
    c.le
    @2
    @1
    @10
    isposd.l
    breqd
    imbi12d
    3anbi123d
    raleqbidv
    raleqbidv
    raleqbidv
    anbi2d
    mpbi2and
    vx
    vy
    vz
    @16
    cK
    @2
    @16
    eqid
    @2
    eqid
    ispos
    sylibr
end
