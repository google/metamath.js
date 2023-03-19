include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "reu3.mm"
include "anbi12i.mm"
include "a1i.mm"
include "an4.mm"
include "rexcom.mm"
include "anbi2i.mm"
include "anidm.mm"
include "bitri.mm"
include "cv.mm"
include "wcel.mm"
include "r19.26.mm"
include "nfra1.mm"
include "r19.3rz.mm"
include "bicomd.mm"
include "adantr.mm"
include "anbi2d.mm"
include "jcab.mm"
include "ralbii.mm"
include "bitr4d.mm"
include "syl5rbb.mm"
include "ad2antlr.mm"
include "ralcom.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "ralbidv.mm"
include "r19.23v.mm"
include "2ralbii.mm"
include "wceq.mm"
include "wn.mm"
include "wo.mm"
include "neneq.mm"
include "anim12i.mm"
include "olcd.mm"
include "dfbi3.mm"
include "sylibr.mm"
include "nfre1.mm"
include "nfv.mm"
include "nfim.mm"
include "raaan2.mm"
include "syl.mm"
include "3bitrd.mm"
include "2rexbidva.mm"
include "reeanv.mm"
include "syl6rbb.mm"

theorem 2reu4a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint w z
  disjoint ph z
  disjoint ph w
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint k x
  assert |- ( ( A =/= (/) /\ B =/= (/) ) -> ( ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) <-> ( E. x e. A E. y e. B ph /\ E. z e. A E. w e. B A. x e. A A. y e. B ( ph -> ( x = z /\ y = w ) ) ) ) )

  proof
    cA
    c0
    wne
    #
    cB
    c0
    wne
    #
    wa
    #
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    wreu
    #
    wa
    #
    @3
    vx
    cA
    wrex
    #
    @3
    vx
    vz
    weq
    #
    wi
    #
    vx
    cA
    wral
    #
    vz
    cA
    wrex
    #
    wa
    #
    @5
    vy
    cB
    wrex
    #
    @5
    vy
    vw
    weq
    #
    wi
    #
    vy
    cB
    wral
    #
    vw
    cB
    wrex
    #
    wa
    #
    wa
    #
    @8
    @14
    wa
    #
    @12
    @18
    wa
    #
    wa
    #
    @8
    wph
    @9
    @15
    wa
    wi
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    vw
    cB
    wrex
    vz
    cA
    wrex
    #
    wa
    @7
    @20
    wb
    @2
    @4
    @13
    @6
    @19
    @3
    vx
    vz
    cA
    reu3
    @5
    vy
    vw
    cB
    reu3
    anbi12i
    a1i
    @20
    @23
    wb
    @2
    @8
    @12
    @14
    @18
    an4
    a1i
    @2
    @21
    @8
    @22
    @27
    @21
    @8
    wb
    @2
    @21
    @8
    @8
    wa
    @8
    @14
    @8
    @8
    wph
    vy
    vx
    cB
    cA
    rexcom
    anbi2i
    @8
    anidm
    bitri
    a1i
    @2
    @27
    @11
    @17
    wa
    #
    vw
    cB
    wrex
    vz
    cA
    wrex
    @22
    @2
    @26
    @28
    vz
    vw
    cA
    cB
    @2
    vz
    cv
    cA
    wcel
    vw
    cv
    cB
    wcel
    wa
    #
    wa
    #
    @26
    wph
    @9
    wi
    #
    vy
    cB
    wral
    #
    wph
    @15
    wi
    #
    vx
    cA
    wral
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    @10
    @16
    wa
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    @28
    @30
    @26
    @32
    @33
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cA
    wral
    #
    @37
    @43
    @32
    vx
    cA
    wral
    #
    @41
    vx
    cA
    wral
    #
    wa
    #
    @30
    @26
    @32
    @41
    vx
    cA
    r19.26
    @30
    @46
    @44
    @41
    wa
    #
    @26
    @30
    @45
    @41
    @44
    @2
    @45
    @41
    wb
    #
    @29
    @0
    @48
    @1
    @0
    @41
    @45
    @41
    vx
    cA
    @40
    vx
    cA
    nfra1
    r19.3rz
    bicomd
    adantr
    adantr
    anbi2d
    @26
    @47
    wb
    @30
    @26
    @32
    @40
    wa
    #
    vx
    cA
    wral
    @47
    @25
    @49
    vx
    cA
    @25
    @31
    @33
    wa
    #
    vy
    cB
    wral
    @49
    @24
    @50
    vy
    cB
    wph
    @9
    @15
    jcab
    ralbii
    @31
    @33
    vy
    cB
    r19.26
    bitri
    ralbii
    @32
    @40
    vx
    cA
    r19.26
    bitri
    a1i
    bitr4d
    syl5rbb
    @30
    @36
    @42
    vx
    cA
    @36
    @32
    vy
    cB
    wral
    #
    @34
    vy
    cB
    wral
    #
    wa
    @30
    @42
    @32
    @34
    vy
    cB
    r19.26
    @30
    @51
    @32
    @52
    @41
    @30
    @32
    @51
    @1
    @32
    @51
    wb
    @0
    @29
    @32
    vy
    cB
    @31
    vy
    cB
    nfra1
    r19.3rz
    ad2antlr
    bicomd
    @52
    @41
    wb
    @30
    @33
    vy
    vx
    cB
    cA
    ralcom
    a1i
    anbi12d
    syl5bb
    ralbidv
    bitr4d
    @37
    @39
    wb
    @30
    @35
    @38
    vx
    vy
    cA
    cB
    @32
    @10
    @34
    @16
    wph
    @9
    vy
    cB
    r19.23v
    wph
    @15
    vx
    cA
    r19.23v
    anbi12i
    2ralbii
    a1i
    @2
    @39
    @28
    wb
    #
    @29
    @2
    cA
    c0
    wceq
    #
    cB
    c0
    wceq
    #
    wb
    #
    @53
    @2
    @54
    @55
    wa
    #
    @54
    wn
    #
    @55
    wn
    #
    wa
    #
    wo
    @56
    @2
    @60
    @57
    @0
    @58
    @1
    @59
    cA
    c0
    neneq
    cB
    c0
    neneq
    anim12i
    olcd
    @54
    @55
    dfbi3
    sylibr
    @10
    @16
    vx
    vy
    cA
    cB
    @3
    @9
    vy
    wph
    vy
    cB
    nfre1
    @9
    vy
    nfv
    nfim
    @5
    @15
    vx
    wph
    vx
    cA
    nfre1
    @15
    vx
    nfv
    nfim
    raaan2
    syl
    adantr
    3bitrd
    2rexbidva
    @11
    @17
    vz
    vw
    cA
    cB
    reeanv
    syl6rbb
    anbi12d
    3bitrd
end
