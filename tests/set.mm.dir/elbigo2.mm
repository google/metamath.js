include "cr.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cbigo.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cdm.mm"
include "cpnf.mm"
include "cico.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cpm.mm"
include "w3a.mm"
include "elbigo.mm"
include "df-3an.mm"
include "bitri.mm"
include "wb.mm"
include "cvv.mm"
include "reex.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "simpl.mm"
include "adantl.mm"
include "sstr2.mm"
include "adantld.mm"
include "impcom.mm"
include "elpm2r.mm"
include "syl12anc.mm"
include "syl2anc.mm"
include "ibar.mm"
include "bicomd.mm"
include "syl5bb.mm"
include "elin.mm"
include "wceq.mm"
include "fdm.mm"
include "ad2antrl.mm"
include "ad2antrr.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "elicopnf.mm"
include "ad3antlr.mm"
include "sselda.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "ralbidv2.mm"
include "rexbidva.mm"

theorem elbigo2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vm: setvar m
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vf: setvar f
  let cC: class C
  let cM: class M
  let vk: setvar k

  disjoint G x
  disjoint G m
  disjoint G y
  disjoint m x
  disjoint x y
  disjoint m y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint G g
  disjoint G f
  disjoint f g
  disjoint g x
  disjoint g m
  disjoint g y
  disjoint f x
  disjoint f m
  disjoint f y
  disjoint F f
  disjoint C m
  disjoint C x
  disjoint C y
  disjoint M m
  disjoint M x
  disjoint k x
  assert |- ( ( ( G : A --> RR /\ A C_ RR ) /\ ( F : B --> RR /\ B C_ A ) ) -> ( F e. ( _O ` G ) <-> E. x e. RR E. m e. RR A. y e. B ( x <_ y -> ( F ` y ) <_ ( m x. ( G ` y ) ) ) ) )

  proof
    cA
    cr
    cG
    wf
    #
    cA
    cr
    wss
    #
    wa
    #
    cB
    cr
    cF
    wf
    #
    cB
    cA
    wss
    #
    wa
    #
    wa
    #
    cF
    cG
    cbigo
    cfv
    wcel
    #
    vy
    cv
    #
    cF
    cfv
    vm
    cv
    #
    @8
    cG
    cfv
    cmul
    co
    cle
    wbr
    #
    vy
    cF
    cdm
    #
    vx
    cv
    #
    cpnf
    cico
    co
    #
    cin
    #
    wral
    #
    vm
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    @12
    @8
    cle
    wbr
    #
    @10
    wi
    #
    vy
    cB
    wral
    #
    vm
    cr
    wrex
    #
    vx
    cr
    wrex
    @7
    cF
    cr
    cr
    cpm
    co
    #
    wcel
    #
    cG
    @22
    wcel
    #
    wa
    #
    @17
    wa
    #
    @6
    @17
    @7
    @23
    @24
    @17
    w3a
    @26
    vx
    vy
    vm
    cF
    cG
    elbigo
    @23
    @24
    @17
    df-3an
    bitri
    @6
    @23
    @24
    @26
    @17
    wb
    @6
    cr
    cvv
    wcel
    #
    @27
    wa
    #
    @3
    cB
    cr
    wss
    #
    @23
    @28
    @6
    @27
    @27
    reex
    reex
    pm3.2i
    a1i
    #
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    @5
    @2
    @29
    @4
    @2
    @29
    wi
    @3
    @4
    @1
    @29
    @0
    cB
    cA
    cr
    sstr2
    adantld
    adantl
    impcom
    #
    cr
    cr
    cB
    cF
    cvv
    cvv
    elpm2r
    syl12anc
    @6
    @28
    @2
    @24
    @30
    @2
    @5
    simpl
    cr
    cr
    cA
    cG
    cvv
    cvv
    elpm2r
    syl2anc
    @25
    @17
    @26
    @25
    @17
    ibar
    bicomd
    syl2anc
    syl5bb
    @6
    @16
    @21
    vx
    cr
    @6
    @12
    cr
    wcel
    #
    wa
    #
    @15
    @20
    vm
    cr
    @33
    @9
    cr
    wcel
    #
    wa
    #
    @10
    @19
    vy
    @14
    cB
    @35
    @8
    @14
    wcel
    #
    @10
    wi
    @8
    cB
    wcel
    #
    @18
    wa
    #
    @10
    wi
    @37
    @19
    wi
    @35
    @36
    @38
    @10
    @36
    @8
    @11
    wcel
    #
    @8
    @13
    wcel
    #
    wa
    #
    @35
    @38
    @8
    @11
    @13
    elin
    @35
    @41
    @37
    @40
    wa
    @38
    @35
    @39
    @37
    @40
    @35
    @11
    cB
    @8
    @6
    @11
    cB
    wceq
    #
    @32
    @34
    @3
    @42
    @2
    @4
    cB
    cr
    cF
    fdm
    ad2antrl
    ad2antrr
    eleq2d
    anbi1d
    @35
    @37
    @40
    @18
    @35
    @37
    wa
    #
    @40
    @8
    cr
    wcel
    #
    @18
    wa
    #
    @18
    @32
    @40
    @45
    wb
    @6
    @34
    @37
    @12
    @8
    elicopnf
    ad3antlr
    @43
    @44
    @18
    @35
    cB
    cr
    @8
    @6
    @29
    @32
    @34
    @31
    ad2antrr
    sselda
    biantrurd
    bitr4d
    pm5.32da
    bitrd
    syl5bb
    imbi1d
    @37
    @18
    @10
    impexp
    syl6bb
    ralbidv2
    rexbidva
    rexbidva
    bitrd
end
