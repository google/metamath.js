include "cli.mm"
include "cfv.mm"
include "cprod.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "climdm.mm"
include "sylib.mm"
include "cmul.mm"
include "cmpt.mm"
include "cseq.mm"
include "cv.mm"
include "prodfc.mm"
include "wa.mm"
include "eqidd.mm"
include "cc.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "iprod.mm"
include "syl5eqr.mm"
include "cio.mm"
include "cvv.mm"
include "seqex.mm"
include "a1i.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "cuz.mm"
include "fzssuz.mm"
include "sseqtr4i.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5reqr.mm"
include "prodeq2i.mm"
include "eqtri.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "sylan2.mm"
include "adantlr.mm"
include "fprodser.mm"
include "eqtr2d.mm"
include "climeq.mm"
include "iotabidv.mm"
include "df-fv.mm"
include "3eqtr4g.mm"
include "eqtrd.mm"
include "breqtrrd.mm"

theorem iprodclim3
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vx: setvar x
  assume iprodclim3.1: |- Z = ( ZZ>= ` M )
  assume iprodclim3.2: |- ( ph -> M e. ZZ )
  assume iprodclim3.3: |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , ( k e. Z |-> A ) ) ~~> y ) )
  assume iprodclim3.4: |- ( ph -> F e. dom ~~> )
  assume iprodclim3.5: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume iprodclim3.6: |- ( ( ph /\ j e. Z ) -> ( F ` j ) = prod_ k e. ( M ... j ) A )

  disjoint A j
  disjoint A n
  disjoint A y
  disjoint F j
  disjoint j k
  disjoint j ph
  disjoint k n
  disjoint k ph
  disjoint k y
  disjoint M j
  disjoint M y
  disjoint n ph
  disjoint n y
  disjoint ph y
  disjoint Z j
  disjoint Z k
  disjoint Z n
  disjoint Z y
  disjoint M k
  disjoint A m
  disjoint A x
  disjoint F x
  disjoint j x
  disjoint k m
  disjoint k x
  disjoint M m
  disjoint m n
  disjoint m ph
  disjoint M x
  disjoint m y
  disjoint ph x
  disjoint Z m
  disjoint Z x
  disjoint j m
  assert |- ( ph -> F ~~> prod_ k e. Z A )

  proof
    wph
    cF
    cF
    cli
    cfv
    #
    cZ
    cA
    vk
    cprod
    #
    cli
    wph
    cF
    cli
    cdm
    #
    wcel
    cF
    @0
    cli
    wbr
    iprodclim3.4
    cF
    climdm
    sylib
    wph
    @1
    cmul
    vk
    cZ
    cA
    cmpt
    #
    cM
    cseq
    #
    cli
    cfv
    #
    @0
    wph
    @1
    cZ
    vm
    cv
    #
    @3
    cfv
    #
    vm
    cprod
    @5
    cZ
    cA
    vm
    vk
    prodfc
    wph
    vy
    @7
    vm
    vn
    @3
    cM
    cZ
    iprodclim3.1
    iprodclim3.2
    iprodclim3.3
    wph
    @6
    cZ
    wcel
    #
    wa
    @7
    eqidd
    wph
    cZ
    cc
    @6
    @3
    wph
    vk
    cZ
    cA
    cc
    @3
    iprodclim3.5
    @3
    eqid
    fmptd
    ffvelrnda
    #
    iprod
    syl5eqr
    wph
    @4
    vx
    cv
    #
    cli
    wbr
    #
    vx
    cio
    cF
    @10
    cli
    wbr
    #
    vx
    cio
    @5
    @0
    wph
    @11
    @12
    vx
    wph
    @10
    vj
    @4
    cF
    cM
    cvv
    @2
    cZ
    iprodclim3.1
    @4
    cvv
    wcel
    wph
    cmul
    @3
    cM
    seqex
    a1i
    iprodclim3.4
    iprodclim3.2
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @13
    cF
    cfv
    cM
    @13
    cfz
    co
    #
    cA
    vk
    cprod
    #
    @13
    @4
    cfv
    #
    iprodclim3.6
    @15
    @17
    @16
    @7
    vm
    cprod
    #
    @18
    @19
    @16
    @6
    vk
    @16
    cA
    cmpt
    #
    cfv
    #
    vm
    cprod
    @17
    @16
    @7
    @21
    vm
    @6
    @16
    wcel
    #
    @21
    @6
    @3
    @16
    cres
    #
    cfv
    @7
    @6
    @23
    @20
    @16
    cZ
    wss
    @23
    @20
    wceq
    @16
    cM
    cuz
    cfv
    #
    cZ
    cM
    @13
    fzssuz
    iprodclim3.1
    sseqtr4i
    vk
    cZ
    @16
    cA
    resmpt
    ax-mp
    fveq1i
    @6
    @16
    @3
    fvres
    syl5reqr
    prodeq2i
    @16
    cA
    vm
    vk
    prodfc
    eqtri
    @15
    @7
    vm
    @3
    cM
    @13
    @15
    @22
    wa
    @7
    eqidd
    @15
    @13
    cZ
    @24
    wph
    @14
    simpr
    iprodclim3.1
    syl6eleq
    wph
    @22
    @7
    cc
    wcel
    #
    @14
    @22
    wph
    @8
    @25
    @22
    @6
    @24
    cZ
    @6
    cM
    @13
    elfzuz
    iprodclim3.1
    syl6eleqr
    @9
    sylan2
    adantlr
    fprodser
    syl5eqr
    eqtr2d
    climeq
    iotabidv
    vx
    @4
    cli
    df-fv
    vx
    cF
    cli
    df-fv
    3eqtr4g
    eqtrd
    breqtrrd
end
