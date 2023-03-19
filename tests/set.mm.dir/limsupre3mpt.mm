include "cmpt.mm"
include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "nfmpt1.mm"
include "cxr.mm"
include "fmptd2f.mm"
include "limsupre3.mm"
include "wceq.mm"
include "eqid.mm"
include "a1i.mm"
include "fvmpt2d.mm"
include "breq2d.mm"
include "anbi2d.mm"
include "rexbida.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "ralbida.mm"
include "anbi12d.mm"
include "wb.mm"
include "breq1.mm"
include "anbi1d.mm"
include "cbvralv.mm"
include "bitrd.mm"
include "cbvrexv.mm"
include "breq2.mm"
include "imbi1d.mm"
include "anbi12i.mm"
include "3bitrd.mm"

theorem limsupre3mpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vj: setvar j
  let vw: setvar w
  assume limsupre3mpt.p: |- F/ x ph
  assume limsupre3mpt.a: |- ( ph -> A C_ RR )
  assume limsupre3mpt.b: |- ( ( ph /\ x e. A ) -> B e. RR* )

  disjoint A k
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B k
  disjoint B y
  disjoint A j
  disjoint A w
  disjoint j k
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint k w
  disjoint w x
  disjoint w y
  disjoint B j
  disjoint B w
  disjoint j ph
  disjoint ph w
  assert |- ( ph -> ( ( limsup ` ( x e. A |-> B ) ) e. RR <-> ( E. y e. RR A. k e. RR E. x e. A ( k <_ x /\ y <_ B ) /\ E. y e. RR E. k e. RR A. x e. A ( k <_ x -> B <_ y ) ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    clsp
    cfv
    cr
    wcel
    vj
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vw
    cv
    #
    @2
    @0
    cfv
    #
    cle
    wbr
    #
    wa
    #
    vx
    cA
    wrex
    #
    vj
    cr
    wral
    #
    vw
    cr
    wrex
    #
    @3
    @5
    @4
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vj
    cr
    wrex
    #
    vw
    cr
    wrex
    #
    wa
    @3
    @4
    cB
    cle
    wbr
    #
    wa
    #
    vx
    cA
    wrex
    #
    vj
    cr
    wral
    #
    vw
    cr
    wrex
    #
    @3
    cB
    @4
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vj
    cr
    wrex
    #
    vw
    cr
    wrex
    #
    wa
    #
    vk
    cv
    #
    @2
    cle
    wbr
    #
    vy
    cv
    #
    cB
    cle
    wbr
    #
    wa
    #
    vx
    cA
    wrex
    #
    vk
    cr
    wral
    #
    vy
    cr
    wrex
    #
    @28
    cB
    @29
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vk
    cr
    wrex
    #
    vy
    cr
    wrex
    #
    wa
    #
    wph
    vw
    cA
    vx
    vj
    @0
    vx
    cA
    cB
    nfmpt1
    limsupre3mpt.a
    wph
    vx
    cA
    cB
    cxr
    limsupre3mpt.p
    limsupre3mpt.b
    fmptd2f
    limsupre3
    wph
    @10
    @20
    @15
    @25
    wph
    @9
    @19
    vw
    cr
    wph
    @8
    @18
    vj
    cr
    wph
    @7
    @17
    vx
    cA
    limsupre3mpt.p
    wph
    @2
    cA
    wcel
    wa
    #
    @6
    @16
    @3
    @41
    @5
    cB
    @4
    cle
    wph
    vx
    cA
    cB
    @0
    cxr
    @0
    @0
    wceq
    wph
    @0
    eqid
    a1i
    limsupre3mpt.b
    fvmpt2d
    #
    breq2d
    anbi2d
    rexbida
    ralbidv
    rexbidv
    wph
    @14
    @24
    vw
    cr
    wph
    @13
    @23
    vj
    cr
    wph
    @12
    @22
    vx
    cA
    limsupre3mpt.p
    @41
    @11
    @21
    @3
    @41
    @5
    cB
    @4
    cle
    @42
    breq1d
    imbi2d
    ralbida
    rexbidv
    rexbidv
    anbi12d
    @26
    @40
    wb
    wph
    @20
    @34
    @25
    @39
    @19
    @33
    vw
    vy
    cr
    @4
    @29
    wceq
    #
    @19
    @3
    @30
    wa
    #
    vx
    cA
    wrex
    #
    vj
    cr
    wral
    #
    @33
    @43
    @18
    @45
    vj
    cr
    @43
    @17
    @44
    vx
    cA
    @43
    @16
    @30
    @3
    @4
    @29
    cB
    cle
    breq1
    anbi2d
    rexbidv
    ralbidv
    @46
    @33
    wb
    @43
    @45
    @32
    vj
    vk
    cr
    @1
    @27
    wceq
    #
    @44
    @31
    vx
    cA
    @47
    @3
    @28
    @30
    @1
    @27
    @2
    cle
    breq1
    #
    anbi1d
    rexbidv
    cbvralv
    a1i
    bitrd
    cbvrexv
    @24
    @38
    vw
    vy
    cr
    @43
    @24
    @3
    @35
    wi
    #
    vx
    cA
    wral
    #
    vj
    cr
    wrex
    #
    @38
    @43
    @23
    @50
    vj
    cr
    @43
    @22
    @49
    vx
    cA
    @43
    @21
    @35
    @3
    @4
    @29
    cB
    cle
    breq2
    imbi2d
    ralbidv
    rexbidv
    @51
    @38
    wb
    @43
    @50
    @37
    vj
    vk
    cr
    @47
    @49
    @36
    vx
    cA
    @47
    @3
    @28
    @35
    @48
    imbi1d
    ralbidv
    cbvrexv
    a1i
    bitrd
    cbvrexv
    anbi12i
    a1i
    3bitrd
end
