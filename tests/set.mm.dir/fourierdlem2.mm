include "cn.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "cr.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "raleqdv.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "breq12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem fourierdlem2
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vi: setvar i
  let vm: setvar m
  let cM: class M
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem2.1: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )

  disjoint A m
  disjoint A p
  disjoint m p
  disjoint B m
  disjoint B p
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint i m
  disjoint i p
  disjoint Q i
  disjoint Q p
  disjoint k x
  assert |- ( M e. NN -> ( Q e. ( P ` M ) <-> ( Q e. ( RR ^m ( 0 ... M ) ) /\ ( ( ( Q ` 0 ) = A /\ ( Q ` M ) = B ) /\ A. i e. ( 0 ..^ M ) ( Q ` i ) < ( Q ` ( i + 1 ) ) ) ) ) )

  proof
    cM
    cn
    wcel
    #
    cQ
    cM
    cP
    cfv
    #
    wcel
    cQ
    cc0
    vp
    cv
    #
    cfv
    #
    cA
    wceq
    #
    cM
    @2
    cfv
    #
    cB
    wceq
    #
    wa
    #
    vi
    cv
    #
    @2
    cfv
    #
    @8
    c1
    caddc
    co
    #
    @2
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    #
    wa
    #
    vp
    cr
    cc0
    cM
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    wcel
    cQ
    @17
    wcel
    cc0
    cQ
    cfv
    #
    cA
    wceq
    #
    cM
    cQ
    cfv
    #
    cB
    wceq
    #
    wa
    #
    @8
    cQ
    cfv
    #
    @10
    cQ
    cfv
    #
    clt
    wbr
    #
    vi
    @13
    wral
    #
    wa
    #
    wa
    @0
    @1
    @18
    cQ
    vm
    cM
    @4
    vm
    cv
    #
    @2
    cfv
    #
    cB
    wceq
    #
    wa
    #
    @12
    vi
    cc0
    @29
    cfzo
    co
    #
    wral
    #
    wa
    #
    vp
    cr
    cc0
    @29
    cfz
    co
    #
    cmap
    co
    #
    crab
    @18
    cn
    cP
    @29
    cM
    wceq
    #
    @35
    @15
    vp
    @37
    @17
    @38
    @36
    @16
    cr
    cmap
    @29
    cM
    cc0
    cfz
    oveq2
    oveq2d
    @38
    @32
    @7
    @34
    @14
    @38
    @31
    @6
    @4
    @38
    @30
    @5
    cB
    @29
    cM
    @2
    fveq2
    eqeq1d
    anbi2d
    @38
    @12
    vi
    @33
    @13
    @29
    cM
    cc0
    cfzo
    oveq2
    raleqdv
    anbi12d
    rabeqbidv
    fourierdlem2.1
    @15
    vp
    @17
    cr
    @16
    cmap
    ovex
    rabex
    fvmpt
    eleq2d
    @15
    @28
    vp
    cQ
    @17
    @2
    cQ
    wceq
    #
    @7
    @23
    @14
    @27
    @39
    @4
    @20
    @6
    @22
    @39
    @3
    @19
    cA
    cc0
    @2
    cQ
    fveq1
    eqeq1d
    @39
    @5
    @21
    cB
    cM
    @2
    cQ
    fveq1
    eqeq1d
    anbi12d
    @39
    @12
    @26
    vi
    @13
    @39
    @9
    @24
    @11
    @25
    clt
    @8
    @2
    cQ
    fveq1
    @10
    @2
    cQ
    fveq1
    breq12d
    ralbidv
    anbi12d
    elrab
    syl6bb
end
