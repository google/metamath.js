include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "crab.mm"
include "crio.mm"
include "mirfv.mm"
include "wreu.mm"
include "mirreu3.mm"
include "riotacl2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylib.mm"
include "simprrd.mm"

theorem mirbtwn
  let wph: wff ph
  let cA: class A
  let cB: class B
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
  assume mirfv.b: |- ( ph -> B e. P )


  assert |- ( ph -> A e. ( ( M ` B ) I B ) )

  proof
    wph
    cB
    cM
    cfv
    #
    cP
    wcel
    #
    cA
    @0
    c.mi
    co
    #
    cA
    cB
    c.mi
    co
    #
    wceq
    #
    cA
    @0
    cB
    cI
    co
    #
    wcel
    #
    wph
    @0
    cA
    vz
    cv
    #
    c.mi
    co
    #
    @3
    wceq
    #
    cA
    @7
    cB
    cI
    co
    #
    wcel
    #
    wa
    #
    vz
    cP
    crab
    #
    wcel
    @1
    @4
    @6
    wa
    #
    wa
    wph
    @0
    @12
    vz
    cP
    crio
    #
    @13
    wph
    vz
    cA
    cB
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
    mirval.a
    mirfv.m
    mirfv.b
    mirfv
    wph
    @12
    vz
    cP
    wreu
    @15
    @13
    wcel
    wph
    cB
    cP
    cG
    cI
    cA
    c.mi
    vz
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    mirfv.b
    mirval.a
    mirreu3
    @12
    vz
    cP
    riotacl2
    syl
    eqeltrd
    @12
    @14
    vz
    @0
    cP
    @7
    @0
    wceq
    #
    @9
    @4
    @11
    @6
    @16
    @8
    @2
    @3
    @7
    @0
    cA
    c.mi
    oveq2
    eqeq1d
    @16
    @10
    @5
    cA
    @7
    @0
    cB
    cI
    oveq1
    eleq2d
    anbi12d
    elrab
    sylib
    simprrd
end
