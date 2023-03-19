include "cismt.mm"
include "co.mm"
include "wcel.mm"
include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "mirf1o.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "miriso.mm"
include "ralrimivva.mm"
include "wb.mm"
include "ismot.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem mirmot
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirmot.m: |- M = ( S ` A )
  assume mirmot.a: |- ( ph -> A e. P )


  assert |- ( ph -> M e. ( G Ismt G ) )

  proof
    wph
    cM
    cG
    cG
    cismt
    co
    wcel
    #
    cP
    cP
    cM
    wf1o
    #
    va
    cv
    #
    cM
    cfv
    vb
    cv
    #
    cM
    cfv
    c.mi
    co
    @2
    @3
    c.mi
    co
    wceq
    #
    vb
    cP
    wral
    va
    cP
    wral
    #
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirmot.a
    mirmot.m
    mirf1o
    wph
    @4
    va
    vb
    cP
    cP
    wph
    @2
    cP
    wcel
    #
    @3
    cP
    wcel
    #
    wa
    #
    wa
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    @2
    @3
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    wph
    cG
    cstrkg
    wcel
    #
    @8
    mirval.g
    adantr
    wph
    cA
    cP
    wcel
    @8
    mirmot.a
    adantr
    mirmot.m
    wph
    @6
    @7
    simprl
    wph
    @6
    @7
    simprr
    miriso
    ralrimivva
    wph
    @9
    @0
    @1
    @5
    wa
    wb
    mirval.g
    cP
    cM
    cG
    c.mi
    cstrkg
    va
    vb
    mirval.p
    mirval.d
    ismot
    syl
    mpbir2and
end
