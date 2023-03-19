include "wcel.mm"
include "cinf.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "ccnv.mm"
include "csup.mm"
include "wor.mm"
include "cnvso.mm"
include "sylib.mm"
include "infcllem.mm"
include "supub.mm"
include "imp.mm"
include "wceq.mm"
include "df-inf.mm"
include "a1i.mm"
include "breq2d.mm"
include "wb.mm"
include "supcl.mm"
include "brcnvg.mm"
include "bicomd.mm"
include "sylan.mm"
include "bitrd.mm"
include "mtbird.mm"
include "ex.mm"

theorem inflb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume infcl.1: |- ( ph -> R Or A )
  assume infcl.2: |- ( ph -> E. x e. A ( A. y e. B -. y R x /\ A. y e. A ( x R y -> E. z e. B z R y ) ) )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ph -> ( C e. B -> -. C R inf ( B , A , R ) ) )

  proof
    wph
    cC
    cB
    wcel
    #
    cC
    cB
    cA
    cR
    cinf
    #
    cR
    wbr
    #
    wn
    wph
    @0
    wa
    #
    @2
    cB
    cA
    cR
    ccnv
    #
    csup
    #
    cC
    @4
    wbr
    #
    wph
    @0
    @6
    wn
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    @4
    wph
    cA
    cR
    wor
    cA
    @4
    wor
    infcl.1
    cA
    cR
    cnvso
    sylib
    #
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    infcl.1
    infcl.2
    infcllem
    #
    supub
    imp
    @3
    @2
    cC
    @5
    cR
    wbr
    #
    @6
    @3
    @1
    @5
    cC
    cR
    @1
    @5
    wceq
    @3
    cB
    cA
    cR
    df-inf
    a1i
    breq2d
    wph
    @5
    cA
    wcel
    #
    @0
    @9
    @6
    wb
    wph
    vx
    vy
    vz
    cA
    cB
    @4
    @7
    @8
    supcl
    @10
    @0
    wa
    @6
    @9
    @5
    cC
    cA
    cB
    cR
    brcnvg
    bicomd
    sylan
    bitrd
    mtbird
    ex
end
