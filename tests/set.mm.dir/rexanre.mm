include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "simpl.mm"
include "imim2i.mm"
include "ralimi.mm"
include "reximi.mm"
include "simpr.mm"
include "jca.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "wcel.mm"
include "cif.mm"
include "ifcl.mm"
include "ancoms.mm"
include "adantl.mm"
include "r19.26.mm"
include "prth.mm"
include "wb.mm"
include "simplrl.mm"
include "simplrr.mm"
include "sselda.mm"
include "maxle.mm"
include "syl3anc.mm"
include "syl5ibr.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "impbid2.mm"

theorem rexanre
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint j ph
  disjoint j ps
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k x
  disjoint k y
  disjoint k z
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
  assert |- ( A C_ RR -> ( E. j e. RR A. k e. A ( j <_ k -> ( ph /\ ps ) ) <-> ( E. j e. RR A. k e. A ( j <_ k -> ph ) /\ E. j e. RR A. k e. A ( j <_ k -> ps ) ) ) )

  proof
    cA
    cr
    wss
    #
    vj
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    wph
    wps
    wa
    #
    wi
    #
    vk
    cA
    wral
    #
    vj
    cr
    wrex
    #
    @3
    wph
    wi
    #
    vk
    cA
    wral
    #
    vj
    cr
    wrex
    #
    @3
    wps
    wi
    #
    vk
    cA
    wral
    #
    vj
    cr
    wrex
    #
    wa
    #
    @7
    @10
    @13
    @6
    @9
    vj
    cr
    @5
    @8
    vk
    cA
    @4
    wph
    @3
    wph
    wps
    simpl
    imim2i
    ralimi
    reximi
    @6
    @12
    vj
    cr
    @5
    @11
    vk
    cA
    @4
    wps
    @3
    wph
    wps
    simpr
    imim2i
    ralimi
    reximi
    jca
    @14
    vx
    cv
    #
    @2
    cle
    wbr
    #
    wph
    wi
    #
    vk
    cA
    wral
    #
    vy
    cv
    #
    @2
    cle
    wbr
    #
    wps
    wi
    #
    vk
    cA
    wral
    #
    wa
    #
    vy
    cr
    wrex
    vx
    cr
    wrex
    #
    @0
    @7
    @14
    @18
    vx
    cr
    wrex
    #
    @22
    vy
    cr
    wrex
    #
    wa
    @24
    @10
    @25
    @13
    @26
    @9
    @18
    vj
    vx
    cr
    @1
    @15
    wceq
    #
    @8
    @17
    vk
    cA
    @27
    @3
    @16
    wph
    @1
    @15
    @2
    cle
    breq1
    imbi1d
    ralbidv
    cbvrexv
    @12
    @22
    vj
    vy
    cr
    @1
    @19
    wceq
    #
    @11
    @21
    vk
    cA
    @28
    @3
    @20
    wps
    @1
    @19
    @2
    cle
    breq1
    imbi1d
    ralbidv
    cbvrexv
    anbi12i
    @18
    @22
    vx
    vy
    cr
    cr
    reeanv
    bitr4i
    @0
    @23
    @7
    vx
    vy
    cr
    cr
    @0
    @15
    cr
    wcel
    #
    @19
    cr
    wcel
    #
    wa
    #
    wa
    #
    @15
    @19
    cle
    wbr
    #
    @19
    @15
    cif
    #
    cr
    wcel
    #
    @23
    @34
    @2
    cle
    wbr
    #
    @4
    wi
    #
    vk
    cA
    wral
    #
    @7
    @31
    @35
    @0
    @30
    @29
    @35
    @33
    @19
    @15
    cr
    ifcl
    ancoms
    adantl
    @23
    @17
    @21
    wa
    #
    vk
    cA
    wral
    @32
    @38
    @17
    @21
    vk
    cA
    r19.26
    @32
    @39
    @37
    vk
    cA
    @39
    @37
    @32
    @2
    cA
    wcel
    #
    wa
    #
    @16
    @20
    wa
    #
    @4
    wi
    @16
    wph
    @20
    wps
    prth
    @41
    @36
    @42
    @4
    @41
    @29
    @30
    @2
    cr
    wcel
    @36
    @42
    wb
    @0
    @29
    @30
    @40
    simplrl
    @0
    @29
    @30
    @40
    simplrr
    @32
    cA
    cr
    @2
    @0
    @31
    simpl
    sselda
    @15
    @19
    @2
    maxle
    syl3anc
    imbi1d
    syl5ibr
    ralimdva
    syl5bir
    @6
    @38
    vj
    @34
    cr
    @1
    @34
    wceq
    #
    @5
    @37
    vk
    cA
    @43
    @3
    @36
    @4
    @1
    @34
    @2
    cle
    breq1
    imbi1d
    ralbidv
    rspcev
    syl6an
    rexlimdvva
    syl5bi
    impbid2
end
