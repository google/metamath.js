include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "wceq.mm"
include "breq1.mm"
include "ralrab.mm"
include "imbi1i.mm"
include "ralbii.mm"
include "anbi12i.mm"
include "cpo.mm"
include "posref.mm"
include "syl2anc.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl5com.mm"
include "mpand.mm"
include "adantr.mm"
include "idd.mm"
include "rgen.mm"
include "breq2.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "mpii.mm"
include "wb.mm"
include "simpr.mm"
include "posasymb.mm"
include "syl3anc.mm"
include "biimpd.mm"
include "ancomsd.mm"
include "syl2and.mm"
include "biimprd.mm"
include "ralrimivw.mm"
include "adantl.mm"
include "pm5.5.mm"
include "bicomd.mm"
include "sylan9bb.mm"
include "syl5ib.mm"
include "adantlr.mm"
include "jca.mm"
include "ex.mm"
include "impbid.mm"
include "syl5bb.mm"

theorem lublecllem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume lublecl.b: |- B = ( Base ` K )
  assume lublecl.l: |- .<_ = ( le ` K )
  assume lublecl.u: |- U = ( lub ` K )
  assume lublecl.k: |- ( ph -> K e. Poset )
  assume lublecl.x: |- ( ph -> X e. B )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .<_ w
  disjoint x y
  disjoint x z
  disjoint .<_ x
  disjoint y z
  disjoint .<_ y
  disjoint .<_ z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint K w
  disjoint K x
  disjoint K z
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint ph w
  disjoint ph x
  assert |- ( ( ph /\ x e. B ) -> ( ( A. z e. { y e. B | y .<_ X } z .<_ x /\ A. w e. B ( A. z e. { y e. B | y .<_ X } z .<_ w -> x .<_ w ) ) <-> x = X ) )

  proof
    vz
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    #
    vz
    vy
    cv
    #
    cX
    c.le
    wbr
    #
    vy
    cB
    crab
    #
    wral
    #
    @0
    vw
    cv
    #
    c.le
    wbr
    #
    vz
    @5
    wral
    #
    @1
    @7
    c.le
    wbr
    #
    wi
    #
    vw
    cB
    wral
    #
    wa
    @0
    cX
    c.le
    wbr
    #
    @2
    wi
    #
    vz
    cB
    wral
    #
    @13
    @8
    wi
    #
    vz
    cB
    wral
    #
    @10
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    wph
    @1
    cB
    wcel
    #
    wa
    #
    @1
    cX
    wceq
    #
    @6
    @15
    @12
    @19
    @4
    @13
    @2
    vz
    vy
    cB
    @3
    @0
    cX
    c.le
    breq1
    #
    ralrab
    @11
    @18
    vw
    cB
    @9
    @17
    @10
    @4
    @13
    @8
    vz
    vy
    cB
    @24
    ralrab
    imbi1i
    ralbii
    anbi12i
    @22
    @20
    @23
    @22
    @15
    cX
    @1
    c.le
    wbr
    #
    @19
    @1
    cX
    c.le
    wbr
    #
    @23
    wph
    @15
    @25
    wi
    @21
    wph
    cX
    cB
    wcel
    #
    @15
    @25
    lublecl.x
    wph
    cX
    cX
    c.le
    wbr
    #
    @27
    @15
    wa
    @25
    wph
    cK
    cpo
    wcel
    #
    @27
    @28
    lublecl.k
    lublecl.x
    cB
    cK
    c.le
    cX
    lublecl.b
    lublecl.l
    posref
    syl2anc
    #
    @14
    @28
    @25
    wi
    vz
    cX
    cB
    @0
    cX
    wceq
    #
    @13
    @28
    @2
    @25
    @0
    cX
    cX
    c.le
    breq1
    #
    @0
    cX
    @1
    c.le
    breq1
    imbi12d
    rspcva
    syl5com
    mpand
    adantr
    wph
    @19
    @26
    wi
    @21
    wph
    @19
    @13
    @13
    wi
    #
    vz
    cB
    wral
    #
    @26
    @33
    vz
    cB
    @0
    cB
    wcel
    @13
    idd
    rgen
    wph
    @27
    @19
    @34
    @26
    wi
    #
    wi
    lublecl.x
    @18
    @35
    vw
    cX
    cB
    @7
    cX
    wceq
    #
    @17
    @34
    @10
    @26
    @36
    @16
    @33
    vz
    cB
    @36
    @8
    @13
    @13
    @7
    cX
    @0
    c.le
    breq2
    imbi2d
    ralbidv
    @7
    cX
    @1
    c.le
    breq2
    imbi12d
    rspcv
    syl
    mpii
    adantr
    @22
    @26
    @25
    @23
    @22
    @26
    @25
    wa
    #
    @23
    @22
    @29
    @21
    @27
    @37
    @23
    wb
    wph
    @29
    @21
    lublecl.k
    adantr
    wph
    @21
    simpr
    wph
    @27
    @21
    lublecl.x
    adantr
    cB
    cK
    c.le
    @1
    cX
    lublecl.b
    lublecl.l
    posasymb
    syl3anc
    biimpd
    ancomsd
    syl2and
    @22
    @23
    @20
    @22
    @23
    wa
    @15
    @19
    @23
    @15
    @22
    @23
    @14
    vz
    cB
    @23
    @2
    @13
    @1
    cX
    @0
    c.le
    breq2
    biimprd
    ralrimivw
    adantl
    wph
    @23
    @19
    @21
    wph
    @23
    wa
    #
    @18
    vw
    cB
    @38
    @27
    @17
    @10
    wph
    @27
    @23
    lublecl.x
    adantr
    @27
    @17
    wa
    @28
    cX
    @7
    c.le
    wbr
    #
    wi
    #
    @38
    @10
    @16
    @40
    vz
    cX
    cB
    @31
    @13
    @28
    @8
    @39
    @32
    @0
    cX
    @7
    c.le
    breq1
    imbi12d
    rspcva
    wph
    @40
    @39
    @23
    @10
    wph
    @28
    @40
    @39
    wb
    @30
    @28
    @39
    pm5.5
    syl
    @23
    @10
    @39
    @1
    cX
    @7
    c.le
    breq1
    bicomd
    sylan9bb
    syl5ib
    mpand
    ralrimivw
    adantlr
    jca
    ex
    impbid
    syl5bb
end
