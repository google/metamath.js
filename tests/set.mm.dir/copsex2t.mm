include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "cop.mm"
include "wcel.mm"
include "nfa1.mm"
include "nfe1.mm"
include "nfv.mm"
include "nfbi.mm"
include "nfa2.mm"
include "nfex.mm"
include "opeq12.mm"
include "copsexg.mm"
include "eqcoms.mm"
include "syl.mm"
include "adantl.mm"
include "2sp.mm"
include "imp.mm"
include "bitr3d.mm"
include "ex.mm"
include "exlimd.mm"
include "elisset.mm"
include "anim12i.mm"
include "eeanv.mm"
include "sylibr.mm"
include "impel.mm"

theorem copsex2t
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W

  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( A. x A. y ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) /\ ( A e. V /\ B e. W ) ) -> ( E. x E. y ( <. A , B >. = <. x , y >. /\ ph ) <-> ps ) )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    vy
    cv
    #
    cB
    wceq
    #
    wa
    #
    wph
    wps
    wb
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @4
    vy
    wex
    #
    vx
    wex
    #
    cA
    cB
    cop
    #
    @0
    @2
    cop
    #
    wceq
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    wps
    wb
    #
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    @8
    @9
    @16
    vx
    @7
    vx
    nfa1
    @15
    wps
    vx
    @14
    vx
    nfe1
    wps
    vx
    nfv
    nfbi
    @8
    @4
    @16
    vy
    @6
    vy
    vx
    nfa2
    @15
    wps
    vy
    @14
    vy
    vx
    @13
    vy
    nfe1
    nfex
    wps
    vy
    nfv
    nfbi
    @8
    @4
    @16
    @8
    @4
    wa
    wph
    @15
    wps
    @4
    wph
    @15
    wb
    #
    @8
    @4
    @12
    @11
    wceq
    @20
    @0
    @2
    cA
    cB
    opeq12
    @20
    @11
    @12
    wph
    vx
    vy
    @11
    copsexg
    eqcoms
    syl
    adantl
    @8
    @4
    @5
    @6
    vx
    vy
    2sp
    imp
    bitr3d
    ex
    exlimd
    exlimd
    @19
    @1
    vx
    wex
    #
    @3
    vy
    wex
    #
    wa
    @10
    @17
    @21
    @18
    @22
    vx
    cA
    cV
    elisset
    vy
    cB
    cW
    elisset
    anim12i
    @1
    @3
    vx
    vy
    eeanv
    sylibr
    impel
end
