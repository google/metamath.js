include "clsxlim.mm"
include "wbr.mm"
include "cli.mm"
include "wa.mm"
include "simpr.mm"
include "cxr.mm"
include "wf.mm"
include "adantr.mm"
include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "xlimxrre.mm"
include "xlimclim2lem.mm"
include "mpbid.mm"
include "climxrre.mm"
include "mpbird.mm"
include "impbida.mm"

theorem xlimclim2
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume xlimclim2.m: |- ( ph -> M e. ZZ )
  assume xlimclim2.z: |- Z = ( ZZ>= ` M )
  assume xlimclim2.f: |- ( ph -> F : Z --> RR* )
  assume xlimclim2.a: |- ( ph -> A e. RR )


  assert |- ( ph -> ( F ~~>* A <-> F ~~> A ) )

  proof
    wph
    cF
    cA
    clsxlim
    wbr
    #
    cF
    cA
    cli
    wbr
    #
    wph
    @0
    wa
    #
    @0
    @1
    wph
    @0
    simpr
    #
    @2
    cA
    vj
    cF
    cM
    cZ
    xlimclim2.z
    wph
    cZ
    cxr
    cF
    wf
    #
    @0
    xlimclim2.f
    adantr
    #
    wph
    cA
    cr
    wcel
    #
    @0
    xlimclim2.a
    adantr
    #
    @2
    cA
    vj
    cF
    cM
    cZ
    wph
    cM
    cz
    wcel
    #
    @0
    xlimclim2.m
    adantr
    xlimclim2.z
    @5
    @7
    @3
    xlimxrre
    xlimclim2lem
    mpbid
    wph
    @1
    wa
    #
    @0
    @1
    wph
    @1
    simpr
    #
    @9
    cA
    vj
    cF
    cM
    cZ
    xlimclim2.z
    wph
    @4
    @1
    xlimclim2.f
    adantr
    #
    wph
    @6
    @1
    xlimclim2.a
    adantr
    #
    @9
    cA
    vj
    cF
    cM
    cZ
    wph
    @8
    @1
    xlimclim2.m
    adantr
    xlimclim2.z
    @11
    @12
    @10
    climxrre
    xlimclim2lem
    mpbird
    impbida
end
