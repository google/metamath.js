include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "co.mm"
include "cvv.mm"
include "cuz.mm"
include "eqid.mm"
include "wcel.mm"
include "cz.mm"
include "syl6eleq.mm"
include "peano2uz.mm"
include "syl.mm"
include "eluzelz.mm"
include "cc.mm"
include "eluzel2.mm"
include "serf.mm"
include "ffvelrnd.mm"
include "seqex.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "syl6eleqr.mm"
include "uztrn2.mm"
include "sylan.mm"
include "cmin.mm"
include "addcl.mm"
include "adantl.mm"
include "w3a.mm"
include "wceq.mm"
include "addass.mm"
include "simpr.mm"
include "cfz.mm"
include "elfzuz.mm"
include "sylan2.mm"
include "adantlr.mm"
include "seqsplit.mm"
include "oveq1d.mm"
include "syldan.mm"
include "ffvelrnda.mm"
include "pncan2d.mm"
include "eqtr2d.mm"
include "climsubc1.mm"

theorem clim2ser
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vj: setvar j
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cG: class G
  assume clim2ser.1: |- Z = ( ZZ>= ` M )
  assume clim2ser.2: |- ( ph -> N e. Z )
  assume clim2ser.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume clim2ser.5: |- ( ph -> seq M ( + , F ) ~~> A )

  disjoint A k
  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint Z k
  disjoint j k
  disjoint A j
  disjoint B j
  disjoint B k
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M j
  disjoint M x
  disjoint M y
  disjoint N j
  disjoint N x
  disjoint N y
  disjoint C j
  disjoint C k
  disjoint C x
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint ph x
  disjoint ph y
  disjoint Z j
  disjoint Z x
  assert |- ( ph -> seq ( N + 1 ) ( + , F ) ~~> ( A - ( seq M ( + , F ) ` N ) ) )

  proof
    wph
    cA
    cN
    caddc
    cF
    cM
    cseq
    #
    cfv
    #
    vj
    @0
    caddc
    cF
    cN
    c1
    caddc
    co
    #
    cseq
    #
    @2
    cvv
    @2
    cuz
    cfv
    #
    @4
    eqid
    #
    wph
    @2
    cM
    cuz
    cfv
    #
    wcel
    #
    @2
    cz
    wcel
    wph
    cN
    @6
    wcel
    #
    @7
    wph
    cN
    cZ
    @6
    clim2ser.2
    clim2ser.1
    syl6eleq
    #
    cM
    cN
    peano2uz
    syl
    #
    cM
    @2
    eluzelz
    syl
    #
    clim2ser.5
    wph
    cZ
    cc
    cN
    @0
    wph
    vk
    cF
    cM
    cZ
    clim2ser.1
    wph
    @8
    cM
    cz
    wcel
    @9
    cM
    cN
    eluzel2
    syl
    clim2ser.4
    serf
    #
    clim2ser.2
    ffvelrnd
    #
    @3
    cvv
    wcel
    wph
    caddc
    cF
    @2
    seqex
    a1i
    wph
    vj
    cv
    #
    @4
    wcel
    #
    wa
    #
    cZ
    cc
    @14
    @0
    wph
    cZ
    cc
    @0
    wf
    @15
    @12
    adantr
    wph
    @2
    cZ
    wcel
    #
    @15
    @14
    cZ
    wcel
    wph
    @2
    @6
    cZ
    @10
    clim2ser.1
    syl6eleqr
    #
    cM
    @14
    @2
    cZ
    clim2ser.1
    uztrn2
    sylan
    ffvelrnd
    @16
    @14
    @0
    cfv
    #
    @1
    cmin
    co
    @1
    @14
    @3
    cfv
    #
    caddc
    co
    #
    @1
    cmin
    co
    @20
    @16
    @19
    @21
    @1
    cmin
    @16
    vk
    vx
    vy
    caddc
    cc
    cF
    cM
    cN
    @14
    vk
    cv
    #
    cc
    wcel
    #
    vx
    cv
    #
    cc
    wcel
    #
    wa
    @22
    @24
    caddc
    co
    #
    cc
    wcel
    @16
    @22
    @24
    addcl
    adantl
    @23
    @25
    vy
    cv
    #
    cc
    wcel
    w3a
    @26
    @27
    caddc
    co
    @22
    @24
    @27
    caddc
    co
    caddc
    co
    wceq
    @16
    @22
    @24
    @27
    addass
    adantl
    wph
    @15
    simpr
    wph
    @8
    @15
    @9
    adantr
    wph
    @22
    cM
    @14
    cfz
    co
    wcel
    #
    @22
    cF
    cfv
    cc
    wcel
    #
    @15
    @28
    wph
    @22
    cZ
    wcel
    #
    @29
    @28
    @22
    @6
    cZ
    @22
    cM
    @14
    elfzuz
    clim2ser.1
    syl6eleqr
    clim2ser.4
    sylan2
    adantlr
    seqsplit
    oveq1d
    @16
    @1
    @20
    wph
    @1
    cc
    wcel
    @15
    @13
    adantr
    wph
    @4
    cc
    @14
    @3
    wph
    vk
    cF
    @2
    @4
    @5
    @11
    wph
    @22
    @4
    wcel
    #
    @30
    @29
    wph
    @17
    @31
    @30
    @18
    cM
    @22
    @2
    cZ
    clim2ser.1
    uztrn2
    sylan
    clim2ser.4
    syldan
    serf
    ffvelrnda
    pncan2d
    eqtr2d
    climsubc1
end
