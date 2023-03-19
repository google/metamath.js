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
include "syl6eleqr.mm"
include "uztrn2.mm"
include "sylan.mm"
include "syldan.mm"
include "ffvelrnda.mm"
include "wa.mm"
include "addcl.mm"
include "adantl.mm"
include "w3a.mm"
include "wceq.mm"
include "addass.mm"
include "simpr.mm"
include "adantr.mm"
include "cfz.mm"
include "elfzuz.mm"
include "sylan2.mm"
include "adantlr.mm"
include "seqsplit.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "climaddc1.mm"

theorem clim2ser2
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
  assume clim2ser2.5: |- ( ph -> seq ( N + 1 ) ( + , F ) ~~> A )

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
  assert |- ( ph -> seq M ( + , F ) ~~> ( A + ( seq M ( + , F ) ` N ) ) )

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
    caddc
    cF
    cN
    c1
    caddc
    co
    #
    cseq
    #
    @0
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
    clim2ser2.5
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
    clim2ser.2
    ffvelrnd
    #
    @0
    cvv
    wcel
    wph
    caddc
    cF
    cM
    seqex
    a1i
    wph
    @4
    cc
    vj
    cv
    #
    @3
    wph
    vk
    cF
    @2
    @4
    @5
    @11
    wph
    vk
    cv
    #
    @4
    wcel
    #
    @14
    cZ
    wcel
    #
    @14
    cF
    cfv
    cc
    wcel
    #
    wph
    @2
    cZ
    wcel
    @15
    @16
    wph
    @2
    @6
    cZ
    @10
    clim2ser.1
    syl6eleqr
    cM
    @14
    @2
    cZ
    clim2ser.1
    uztrn2
    sylan
    clim2ser.4
    syldan
    serf
    ffvelrnda
    #
    wph
    @13
    @4
    wcel
    #
    wa
    #
    @13
    @0
    cfv
    @1
    @13
    @3
    cfv
    #
    caddc
    co
    @21
    @1
    caddc
    co
    @20
    vk
    vx
    vy
    caddc
    cc
    cF
    cM
    cN
    @13
    @14
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
    @14
    @23
    caddc
    co
    #
    cc
    wcel
    @20
    @14
    @23
    addcl
    adantl
    @22
    @24
    vy
    cv
    #
    cc
    wcel
    w3a
    @25
    @26
    caddc
    co
    @14
    @23
    @26
    caddc
    co
    caddc
    co
    wceq
    @20
    @14
    @23
    @26
    addass
    adantl
    wph
    @19
    simpr
    wph
    @8
    @19
    @9
    adantr
    wph
    @14
    cM
    @13
    cfz
    co
    wcel
    #
    @17
    @19
    @27
    wph
    @16
    @17
    @27
    @14
    @6
    cZ
    @14
    cM
    @13
    elfzuz
    clim2ser.1
    syl6eleqr
    clim2ser.4
    sylan2
    adantlr
    seqsplit
    @20
    @1
    @21
    wph
    @1
    cc
    wcel
    @19
    @12
    adantr
    @18
    addcomd
    eqtrd
    climaddc1
end
