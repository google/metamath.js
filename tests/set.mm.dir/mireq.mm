include "cfv.mm"
include "mircl.mm"
include "co.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "crio.mm"
include "mirfv.mm"
include "eqtr3d.mm"
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
include "mpbird.mm"
include "simpld.mm"
include "eqcomd.mm"
include "simprd.mm"
include "tgbtwncom.mm"
include "ismir.mm"
include "mirmir.mm"
include "eqtrd.mm"

theorem mireq
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
  let va: setvar a
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )
  assume mirfv.m: |- M = ( S ` A )
  assume mirmir.b: |- ( ph -> B e. P )
  assume mireq.c: |- ( ph -> C e. P )
  assume mireq.d: |- ( ph -> ( M ` B ) = ( M ` C ) )


  assert |- ( ph -> B = C )

  proof
    wph
    cB
    cC
    cM
    cfv
    #
    cM
    cfv
    cC
    wph
    cA
    @0
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
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cC
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    mireq.c
    mircl
    #
    mirmir.b
    wph
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
    wph
    @2
    @3
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
    @4
    @6
    wa
    #
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
    @8
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
    @0
    wceq
    #
    wph
    cB
    cM
    cfv
    @14
    @0
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
    mirmir.b
    mirfv
    mireq.d
    eqtr3d
    wph
    @0
    cP
    wcel
    @13
    vz
    cP
    wreu
    @7
    @15
    wb
    @1
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
    mirmir.b
    mirval.a
    mirreu3
    @13
    @7
    vz
    cP
    @0
    @8
    @0
    wceq
    #
    @10
    @4
    @12
    @6
    @16
    @9
    @2
    @3
    @8
    @0
    cA
    c.mi
    oveq2
    eqeq1d
    @16
    @11
    @5
    cA
    @8
    @0
    cB
    cI
    oveq1
    eleq2d
    anbi12d
    riota2
    syl2anc
    mpbird
    #
    simpld
    eqcomd
    wph
    @0
    cA
    cB
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    @1
    mirval.a
    mirmir.b
    wph
    @4
    @6
    @17
    simprd
    tgbtwncom
    ismir
    wph
    cA
    cC
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
    mireq.c
    mirmir
    eqtrd
end
