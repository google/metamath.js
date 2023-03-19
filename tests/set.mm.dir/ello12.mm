include "cr.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "clo1.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cdm.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cpm.mm"
include "wb.mm"
include "cvv.mm"
include "reex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "ello1.mm"
include "baib.mm"
include "syl.mm"
include "elin.mm"
include "wceq.mm"
include "fdm.mm"
include "ad3antrrr.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "simpllr.mm"
include "elicopnf.mm"
include "sselda.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "ralbidv2.mm"
include "rexbidva.mm"

theorem ello12
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vm: setvar m
  let cF: class F
  let cC: class C
  let vf: setvar f
  let cM: class M

  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint C m
  disjoint C x
  disjoint C y
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint M m
  disjoint M x
  assert |- ( ( F : A --> RR /\ A C_ RR ) -> ( F e. <_O(1) <-> E. x e. RR E. m e. RR A. y e. A ( x <_ y -> ( F ` y ) <_ m ) ) )

  proof
    cA
    cr
    cF
    wf
    #
    cA
    cr
    wss
    #
    wa
    #
    cF
    clo1
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
    @8
    @4
    cle
    wbr
    #
    @6
    wi
    #
    vy
    cA
    wral
    #
    vm
    cr
    wrex
    #
    vx
    cr
    wrex
    @2
    cF
    cr
    cr
    cpm
    co
    wcel
    #
    @3
    @13
    wb
    cr
    cvv
    wcel
    #
    @19
    @2
    @18
    reex
    reex
    cr
    cr
    cA
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    @3
    @18
    @13
    vx
    vy
    vm
    cF
    ello1
    baib
    syl
    @2
    @12
    @17
    vx
    cr
    @2
    @8
    cr
    wcel
    #
    wa
    #
    @11
    @16
    vm
    cr
    @21
    @5
    cr
    wcel
    #
    wa
    #
    @6
    @15
    vy
    @10
    cA
    @23
    @4
    @10
    wcel
    #
    @6
    wi
    @4
    cA
    wcel
    #
    @14
    wa
    #
    @6
    wi
    @25
    @15
    wi
    @23
    @24
    @26
    @6
    @24
    @4
    @7
    wcel
    #
    @4
    @9
    wcel
    #
    wa
    #
    @23
    @26
    @4
    @7
    @9
    elin
    @23
    @29
    @25
    @28
    wa
    @26
    @23
    @27
    @25
    @28
    @23
    @7
    cA
    @4
    @0
    @7
    cA
    wceq
    @1
    @20
    @22
    cA
    cr
    cF
    fdm
    ad3antrrr
    eleq2d
    anbi1d
    @23
    @25
    @28
    @14
    @23
    @25
    wa
    #
    @28
    @4
    cr
    wcel
    #
    @14
    wa
    #
    @14
    @30
    @20
    @28
    @32
    wb
    @2
    @20
    @22
    @25
    simpllr
    @8
    @4
    elicopnf
    syl
    @30
    @31
    @14
    @23
    cA
    cr
    @4
    @0
    @1
    @20
    @22
    simpllr
    sselda
    biantrurd
    bitr4d
    pm5.32da
    bitrd
    syl5bb
    imbi1d
    @25
    @14
    @6
    impexp
    syl6bb
    ralbidv2
    rexbidva
    rexbidva
    bitrd
end
