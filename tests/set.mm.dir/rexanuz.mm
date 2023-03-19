include "wa.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "r19.26.mm"
include "rexbii.mm"
include "r19.40.mm"
include "sylbi.mm"
include "crn.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "uzf.mm"
include "ffn.mm"
include "raleq.mm"
include "rexrn.mm"
include "mp2b.mm"
include "wi.mm"
include "wcel.mm"
include "cin.mm"
include "uzin2.mm"
include "wss.mm"
include "inss1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "inss2.mm"
include "anim12i.mm"
include "sylibr.mm"
include "rspcev.mm"
include "syl2an.mm"
include "an4s.mm"
include "rexlimdvaa.mm"
include "rexlimiva.mm"
include "imp.mm"
include "sylib.mm"
include "syl2anbr.mm"
include "impbii.mm"

theorem rexanuz
  let wph: wff ph
  let wps: wff ps
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint j k
  disjoint j ph
  disjoint j ps
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ( E. j e. ZZ A. k e. ( ZZ>= ` j ) ( ph /\ ps ) <-> ( E. j e. ZZ A. k e. ( ZZ>= ` j ) ph /\ E. j e. ZZ A. k e. ( ZZ>= ` j ) ps ) )

  proof
    wph
    wps
    wa
    #
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    #
    vj
    cz
    wrex
    #
    wph
    vk
    @1
    wral
    #
    vj
    cz
    wrex
    #
    wps
    vk
    @1
    wral
    #
    vj
    cz
    wrex
    #
    wa
    #
    @3
    @4
    @6
    wa
    #
    vj
    cz
    wrex
    @8
    @2
    @9
    vj
    cz
    wph
    wps
    vk
    @1
    r19.26
    rexbii
    @4
    @6
    vj
    cz
    r19.40
    sylbi
    @5
    wph
    vk
    vx
    cv
    #
    wral
    #
    vx
    cuz
    crn
    #
    wrex
    #
    wps
    vk
    vy
    cv
    #
    wral
    #
    vy
    @12
    wrex
    #
    @3
    @7
    cz
    cz
    cpw
    #
    cuz
    wf
    #
    cuz
    cz
    wfn
    #
    @13
    @5
    wb
    uzf
    cz
    @17
    cuz
    ffn
    #
    @11
    @4
    vx
    vj
    cz
    cuz
    wph
    vk
    @10
    @1
    raleq
    rexrn
    mp2b
    @18
    @19
    @16
    @7
    wb
    uzf
    @20
    @15
    @6
    vy
    vj
    cz
    cuz
    wps
    vk
    @14
    @1
    raleq
    rexrn
    mp2b
    @13
    @16
    wa
    @0
    vk
    vz
    cv
    #
    wral
    #
    vz
    @12
    wrex
    #
    @3
    @13
    @16
    @23
    @11
    @16
    @23
    wi
    vx
    @12
    @10
    @12
    wcel
    #
    @11
    wa
    @15
    @23
    vy
    @12
    @24
    @14
    @12
    wcel
    #
    @11
    @15
    @23
    @24
    @25
    wa
    @10
    @14
    cin
    #
    @12
    wcel
    @0
    vk
    @26
    wral
    #
    @23
    @11
    @15
    wa
    #
    @10
    @14
    uzin2
    @28
    wph
    vk
    @26
    wral
    #
    wps
    vk
    @26
    wral
    #
    wa
    @27
    @11
    @29
    @15
    @30
    @26
    @10
    wss
    @11
    @29
    wi
    @10
    @14
    inss1
    wph
    vk
    @26
    @10
    ssralv
    ax-mp
    @26
    @14
    wss
    @15
    @30
    wi
    @10
    @14
    inss2
    wps
    vk
    @26
    @14
    ssralv
    ax-mp
    anim12i
    wph
    wps
    vk
    @26
    r19.26
    sylibr
    @22
    @27
    vz
    @26
    @12
    @0
    vk
    @21
    @26
    raleq
    rspcev
    syl2an
    an4s
    rexlimdvaa
    rexlimiva
    imp
    @18
    @19
    @23
    @3
    wb
    uzf
    @20
    @22
    @2
    vz
    vj
    cz
    cuz
    @0
    vk
    @21
    @1
    raleq
    rexrn
    mp2b
    sylib
    syl2anbr
    impbii
end
