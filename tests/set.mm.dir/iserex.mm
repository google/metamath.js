include "wceq.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "wb.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wi.mm"
include "seqeq1.mm"
include "eleq1d.mm"
include "bicomd.mm"
include "a1i.mm"
include "wa.mm"
include "wbr.mm"
include "simpll.mm"
include "cc.mm"
include "cz.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "syl.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "seqeq1d.mm"
include "simplr.mm"
include "syl6eleqr.mm"
include "cv.mm"
include "sylan.mm"
include "simpr.mm"
include "climdm.mm"
include "sylib.mm"
include "clim2ser.mm"
include "eqbrtrrd.mm"
include "climrel.mm"
include "releldmi.mm"
include "adantr.mm"
include "eqbrtrd.mm"
include "clim2ser2.mm"
include "impbida.mm"
include "ex.mm"
include "wo.mm"
include "uzm1.mm"
include "mpjaod.mm"

theorem iserex
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vj: setvar j
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cG: class G
  assume clim2ser.1: |- Z = ( ZZ>= ` M )
  assume iserex.2: |- ( ph -> N e. Z )
  assume iserex.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )

  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint Z k
  disjoint j k
  disjoint A j
  disjoint A k
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
  assert |- ( ph -> ( seq M ( + , F ) e. dom ~~> <-> seq N ( + , F ) e. dom ~~> ) )

  proof
    wph
    cN
    cM
    wceq
    #
    caddc
    cF
    cM
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    caddc
    cF
    cN
    cseq
    #
    @2
    wcel
    #
    wb
    #
    cN
    c1
    cmin
    co
    #
    cM
    cuz
    cfv
    #
    wcel
    #
    @0
    @6
    wi
    wph
    @0
    @5
    @3
    @0
    @4
    @1
    @2
    caddc
    cF
    cN
    cM
    seqeq1
    eleq1d
    bicomd
    a1i
    wph
    @9
    @6
    wph
    @9
    wa
    #
    @3
    @5
    @10
    @3
    wa
    #
    @4
    @1
    cli
    cfv
    #
    @7
    @1
    cfv
    #
    cmin
    co
    #
    cli
    wbr
    @5
    @11
    caddc
    cF
    @7
    c1
    caddc
    co
    #
    cseq
    #
    @4
    @14
    cli
    @11
    wph
    @16
    @4
    wceq
    #
    wph
    @9
    @3
    simpll
    #
    wph
    @15
    cN
    caddc
    cF
    wph
    cN
    cc
    wcel
    c1
    cc
    wcel
    @15
    cN
    wceq
    wph
    cN
    wph
    cN
    @8
    wcel
    #
    cN
    cz
    wcel
    wph
    cN
    cZ
    @8
    iserex.2
    clim2ser.1
    syl6eleq
    #
    cM
    cN
    eluzelz
    syl
    zcnd
    ax-1cn
    cN
    c1
    npcan
    sylancl
    seqeq1d
    #
    syl
    @11
    @12
    vk
    cF
    cM
    @7
    cZ
    clim2ser.1
    @11
    @7
    @8
    cZ
    wph
    @9
    @3
    simplr
    clim2ser.1
    syl6eleqr
    @11
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    @22
    cF
    cfv
    cc
    wcel
    #
    @18
    iserex.3
    sylan
    @11
    @3
    @1
    @12
    cli
    wbr
    @10
    @3
    simpr
    @1
    climdm
    sylib
    clim2ser
    eqbrtrrd
    @4
    @14
    cli
    climrel
    releldmi
    syl
    @10
    @5
    wa
    #
    @1
    @4
    cli
    cfv
    #
    @13
    caddc
    co
    #
    cli
    wbr
    @3
    @25
    @26
    vk
    cF
    cM
    @7
    cZ
    clim2ser.1
    @10
    @7
    cZ
    wcel
    @5
    @10
    @7
    @8
    cZ
    wph
    @9
    simpr
    clim2ser.1
    syl6eleqr
    adantr
    @25
    wph
    @23
    @24
    wph
    @9
    @5
    simpll
    #
    iserex.3
    sylan
    @25
    @16
    @4
    @26
    cli
    @25
    wph
    @17
    @28
    @21
    syl
    @25
    @5
    @4
    @26
    cli
    wbr
    @10
    @5
    simpr
    @4
    climdm
    sylib
    eqbrtrd
    clim2ser2
    @1
    @27
    cli
    climrel
    releldmi
    syl
    impbida
    ex
    wph
    @19
    @0
    @9
    wo
    @20
    cM
    cN
    uzm1
    syl
    mpjaod
end
