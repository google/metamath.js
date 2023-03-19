include "cph.mm"
include "co.mm"
include "wcel.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cva.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "shseli.mm"
include "biimpi.mm"
include "reeanv.mm"
include "eqtr2.mm"
include "cmv.mm"
include "wb.mm"
include "chil.mm"
include "sheli.mm"
include "anim12i.mm"
include "hvaddsub4.mm"
include "syl2an.mm"
include "an4s.mm"
include "adantll.mm"
include "csh.mm"
include "shsubcl.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "adantl.mm"
include "adantr.mm"
include "jctild.mm"
include "elin.mm"
include "eleq2.mm"
include "syl5bbr.mm"
include "ad2antrr.mm"
include "sylibd.mm"
include "c0v.mm"
include "elch0.mm"
include "hvsubeq0.mm"
include "syl5bb.mm"
include "ad2antlr.mm"
include "sylbid.mm"
include "syl5.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "ralrimivva.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "oveq2.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "reu4.mm"
include "sylibr.mm"

theorem cdjreui
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  let vw: setvar w
  assume cdjreu.1: |- A e. SH
  assume cdjreu.2: |- B e. SH

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  disjoint C z
  disjoint C w
  assert |- ( ( C e. ( A +H B ) /\ ( A i^i B ) = 0H ) -> E! x e. A E. y e. B C = ( x +h y ) )

  proof
    cC
    cA
    cB
    cph
    co
    wcel
    #
    cA
    cB
    cin
    #
    c0h
    wceq
    #
    wa
    cC
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    #
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    @7
    cC
    vz
    cv
    #
    vw
    cv
    #
    cva
    co
    #
    wceq
    #
    vw
    cB
    wrex
    #
    wa
    #
    vx
    vz
    weq
    #
    wi
    #
    vz
    cA
    wral
    vx
    cA
    wral
    #
    wa
    @7
    vx
    cA
    wreu
    @0
    @8
    @2
    @17
    @0
    @8
    vx
    vy
    cA
    cB
    cC
    cdjreu.1
    cdjreu.2
    shseli
    biimpi
    @2
    @16
    vx
    vz
    cA
    cA
    @14
    @6
    @12
    wa
    #
    vw
    cB
    wrex
    vy
    cB
    wrex
    @2
    @3
    cA
    wcel
    #
    @9
    cA
    wcel
    #
    wa
    #
    wa
    #
    @15
    @6
    @12
    vy
    vw
    cB
    cB
    reeanv
    @22
    @18
    @15
    vy
    vw
    cB
    cB
    @18
    @5
    @11
    wceq
    #
    @22
    @4
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    wa
    #
    wa
    #
    @15
    cC
    @5
    @11
    eqtr2
    @27
    @23
    @3
    @9
    cmv
    co
    #
    @10
    @4
    cmv
    co
    #
    wceq
    #
    @15
    @21
    @26
    @23
    @30
    wb
    #
    @2
    @19
    @24
    @20
    @25
    @31
    @19
    @24
    wa
    @3
    chil
    wcel
    #
    @4
    chil
    wcel
    #
    wa
    @9
    chil
    wcel
    #
    @10
    chil
    wcel
    #
    wa
    @31
    @20
    @25
    wa
    @19
    @32
    @24
    @33
    @3
    cA
    cdjreu.1
    sheli
    #
    @4
    cB
    cdjreu.2
    sheli
    anim12i
    @20
    @34
    @25
    @35
    @9
    cA
    cdjreu.1
    sheli
    #
    @10
    cB
    cdjreu.2
    sheli
    anim12i
    @3
    @4
    @9
    @10
    hvaddsub4
    syl2an
    an4s
    adantll
    @27
    @30
    @28
    c0h
    wcel
    #
    @15
    @27
    @30
    @28
    cA
    wcel
    #
    @28
    cB
    wcel
    #
    wa
    #
    @38
    @21
    @26
    @30
    @41
    wi
    @2
    @21
    @26
    wa
    @30
    @40
    @39
    @26
    @30
    @40
    wi
    @21
    @26
    @40
    @30
    @29
    cB
    wcel
    #
    @25
    @24
    @42
    cB
    csh
    wcel
    @25
    @24
    @42
    cdjreu.2
    @10
    @4
    cB
    shsubcl
    mp3an1
    ancoms
    @28
    @29
    cB
    eleq1
    syl5ibrcom
    adantl
    @21
    @39
    @26
    cA
    csh
    wcel
    @19
    @20
    @39
    cdjreu.1
    @3
    @9
    cA
    shsubcl
    mp3an1
    adantr
    jctild
    adantll
    @2
    @41
    @38
    wb
    @21
    @26
    @41
    @28
    @1
    wcel
    @2
    @38
    @28
    cA
    cB
    elin
    @1
    c0h
    @28
    eleq2
    syl5bbr
    ad2antrr
    sylibd
    @21
    @38
    @15
    wb
    #
    @2
    @26
    @19
    @32
    @34
    @43
    @20
    @36
    @37
    @38
    @28
    c0v
    wceq
    @32
    @34
    wa
    @15
    @28
    elch0
    @3
    @9
    hvsubeq0
    syl5bb
    syl2an
    ad2antlr
    sylibd
    sylbid
    syl5
    rexlimdvva
    syl5bir
    ralrimivva
    anim12i
    @7
    @13
    vx
    vz
    cA
    @15
    @7
    cC
    @9
    @4
    cva
    co
    #
    wceq
    #
    vy
    cB
    wrex
    @13
    @15
    @6
    @45
    vy
    cB
    @15
    @5
    @44
    cC
    @3
    @9
    @4
    cva
    oveq1
    eqeq2d
    rexbidv
    @45
    @12
    vy
    vw
    cB
    vy
    vw
    weq
    @44
    @11
    cC
    @4
    @10
    @9
    cva
    oveq2
    eqeq2d
    cbvrexv
    syl6bb
    reu4
    sylibr
end
