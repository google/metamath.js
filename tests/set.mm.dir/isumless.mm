include "csu.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cle.mm"
include "wss.mm"
include "cc.mm"
include "wral.mm"
include "cuz.mm"
include "cfv.mm"
include "cfn.mm"
include "wo.mm"
include "wceq.mm"
include "sselda.mm"
include "wa.mm"
include "recnd.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "eqimssi.mm"
include "orci.mm"
include "a1i.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "cmpt.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "eqid.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "ifeq1d.mm"
include "eqtrd.mm"
include "cr.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "wbr.mm"
include "leid.mm"
include "breq1.mm"
include "ifboth.mm"
include "sylan.mm"
include "syl2anc.mm"
include "fsumcvg3.mm"
include "isumle.mm"
include "eqbrtrd.mm"

theorem isumless
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  assume isumless.1: |- Z = ( ZZ>= ` M )
  assume isumless.2: |- ( ph -> M e. ZZ )
  assume isumless.3: |- ( ph -> A e. Fin )
  assume isumless.4: |- ( ph -> A C_ Z )
  assume isumless.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume isumless.6: |- ( ( ph /\ k e. Z ) -> B e. RR )
  assume isumless.7: |- ( ( ph /\ k e. Z ) -> 0 <_ B )
  assume isumless.8: |- ( ph -> seq M ( + , F ) e. dom ~~> )

  disjoint A k
  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint j k
  disjoint A j
  disjoint F j
  disjoint Z j
  assert |- ( ph -> sum_ k e. A B <_ sum_ k e. Z B )

  proof
    wph
    cA
    cB
    vk
    csu
    #
    cZ
    vk
    cv
    #
    cA
    wcel
    #
    cB
    cc0
    cif
    #
    vk
    csu
    #
    cZ
    cB
    vk
    csu
    cle
    wph
    cA
    cZ
    wss
    cB
    cc
    wcel
    #
    vk
    cA
    wral
    cZ
    cM
    cuz
    cfv
    #
    wss
    #
    cZ
    cfn
    wcel
    #
    wo
    #
    @0
    @4
    wceq
    isumless.4
    wph
    @5
    vk
    cA
    wph
    @2
    @1
    cZ
    wcel
    #
    @5
    wph
    cA
    cZ
    @1
    isumless.4
    sselda
    wph
    @10
    wa
    #
    cB
    isumless.6
    recnd
    syldan
    #
    ralrimiva
    @9
    wph
    @7
    @8
    cZ
    @6
    isumless.1
    eqimssi
    orci
    a1i
    cA
    cZ
    cB
    vk
    cM
    sumss2
    syl21anc
    wph
    @3
    cB
    vk
    vj
    cZ
    vj
    cv
    #
    cA
    wcel
    #
    @13
    cF
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    cF
    cM
    cZ
    isumless.1
    isumless.2
    @11
    @1
    @17
    cfv
    #
    @2
    @1
    cF
    cfv
    #
    cc0
    cif
    #
    @3
    @10
    @18
    @20
    wceq
    wph
    vj
    @1
    @16
    @20
    cZ
    @17
    @13
    @1
    wceq
    @14
    @2
    @15
    @19
    cc0
    @13
    @1
    cA
    eleq1
    @13
    @1
    cF
    fveq2
    ifbieq1d
    @17
    eqid
    @2
    @19
    cc0
    @1
    cF
    fvex
    c0ex
    ifex
    fvmpt
    adantl
    @11
    @2
    @19
    cB
    cc0
    isumless.5
    ifeq1d
    eqtrd
    #
    @11
    cB
    cr
    wcel
    #
    cc0
    cr
    wcel
    @3
    cr
    wcel
    isumless.6
    0re
    @2
    cB
    cc0
    cr
    ifcl
    sylancl
    isumless.5
    isumless.6
    @11
    @22
    cc0
    cB
    cle
    wbr
    #
    @3
    cB
    cle
    wbr
    #
    isumless.6
    isumless.7
    @22
    cB
    cB
    cle
    wbr
    #
    @23
    @24
    cB
    leid
    @2
    @25
    @23
    @24
    cB
    cc0
    cB
    @3
    cB
    cle
    breq1
    cc0
    @3
    cB
    cle
    breq1
    ifboth
    sylan
    syl2anc
    wph
    cA
    cB
    vk
    @17
    cM
    cZ
    isumless.1
    isumless.2
    isumless.3
    isumless.4
    @21
    @12
    fsumcvg3
    isumless.8
    isumle
    eqbrtrd
end
