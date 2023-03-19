include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "crio.mm"
include "mirfv.mm"
include "wreu.mm"
include "wb.mm"
include "mirreu3.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbi2and.mm"
include "eqtr2d.mm"

theorem ismir
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
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
  assume ismir.1: |- ( ph -> C e. P )
  assume ismir.2: |- ( ph -> ( A .- C ) = ( A .- B ) )
  assume ismir.3: |- ( ph -> A e. ( C I B ) )


  assert |- ( ph -> C = ( M ` B ) )

  proof
    wph
    cB
    cM
    cfv
    cA
    vz
    cv
    #
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
    wa
    #
    vz
    cP
    crio
    #
    cC
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
    cA
    cC
    c.mi
    co
    #
    @2
    wceq
    #
    cA
    cC
    cB
    cI
    co
    #
    wcel
    #
    @7
    cC
    wceq
    #
    ismir.2
    ismir.3
    wph
    cC
    cP
    wcel
    @6
    vz
    cP
    wreu
    @9
    @11
    wa
    #
    @12
    wb
    ismir.1
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
    @6
    @13
    vz
    cP
    cC
    @0
    cC
    wceq
    #
    @3
    @9
    @5
    @11
    @14
    @1
    @8
    @2
    @0
    cC
    cA
    c.mi
    oveq2
    eqeq1d
    @14
    @4
    @10
    cA
    @0
    cC
    cB
    cI
    oveq1
    eleq2d
    anbi12d
    riota2
    syl2anc
    mpbi2and
    eqtr2d
end
