include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "crio.mm"
include "cvv.mm"
include "riotaex.mm"
include "a1i.mm"
include "cfv.mm"
include "cmpt.mm"
include "mirval.mm"
include "syl5eq.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "mirfv.mm"
include "wreu.mm"
include "mirreu3.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "fmpt2d.mm"

theorem mirf
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let vg: setvar g
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )
  assume mirfv.m: |- M = ( S ` A )


  assert |- ( ph -> M : P --> P )

  proof
    wph
    vy
    vx
    cP
    cA
    vz
    cv
    #
    c.mi
    co
    #
    cA
    vy
    cv
    #
    c.mi
    co
    wceq
    cA
    @0
    @2
    cI
    co
    wcel
    wa
    #
    vz
    cP
    crio
    #
    cP
    cM
    cvv
    @4
    cvv
    wcel
    wph
    @2
    cP
    wcel
    wa
    @3
    vz
    cP
    riotaex
    a1i
    wph
    cM
    cA
    cS
    cfv
    vy
    cP
    @4
    cmpt
    mirfv.m
    wph
    vy
    vz
    cA
    cP
    cS
    cG
    cI
    cL
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirval
    syl5eq
    wph
    vx
    cv
    #
    cP
    wcel
    #
    wa
    #
    @5
    cM
    cfv
    @1
    cA
    @5
    c.mi
    co
    wceq
    cA
    @0
    @5
    cI
    co
    wcel
    wa
    #
    vz
    cP
    crio
    #
    cP
    @7
    vz
    cA
    @5
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
    wph
    cG
    cstrkg
    wcel
    @6
    mirval.g
    adantr
    #
    wph
    cA
    cP
    wcel
    @6
    mirval.a
    adantr
    #
    mirfv.m
    wph
    @6
    simpr
    #
    mirfv
    @7
    @8
    vz
    cP
    wreu
    @9
    cP
    wcel
    @7
    @5
    cP
    cG
    cI
    cA
    c.mi
    vz
    mirval.p
    mirval.d
    mirval.i
    @10
    @12
    @11
    mirreu3
    @8
    vz
    cP
    riotacl
    syl
    eqeltrd
    fmpt2d
end
