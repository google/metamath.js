include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "cop.mm"
include "wa.mm"
include "wb.mm"
include "elisset.mm"
include "eeanv.mm"
include "nfe1.mm"
include "nfv.mm"
include "nfbi.mm"
include "nfex.mm"
include "opeq12.mm"
include "copsexg.mm"
include "eqcoms.mm"
include "syl.mm"
include "bitr3d.mm"
include "exlimi.mm"
include "sylbir.mm"
include "syl2an.mm"

theorem copsex2g
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume copsex2g.1: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( A e. V /\ B e. W ) -> ( E. x E. y ( <. A , B >. = <. x , y >. /\ ph ) <-> ps ) )

  proof
    cA
    cV
    wcel
    vx
    cv
    #
    cA
    wceq
    #
    vx
    wex
    #
    vy
    cv
    #
    cB
    wceq
    #
    vy
    wex
    #
    cA
    cB
    cop
    #
    @0
    @3
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
    cB
    cW
    wcel
    vx
    cA
    cV
    elisset
    vy
    cB
    cW
    elisset
    @2
    @5
    wa
    @1
    @4
    wa
    #
    vy
    wex
    #
    vx
    wex
    @11
    @1
    @4
    vx
    vy
    eeanv
    @13
    @11
    vx
    @10
    wps
    vx
    @9
    vx
    nfe1
    wps
    vx
    nfv
    nfbi
    @12
    @11
    vy
    @10
    wps
    vy
    @9
    vy
    vx
    @8
    vy
    nfe1
    nfex
    wps
    vy
    nfv
    nfbi
    @12
    wph
    @10
    wps
    @12
    @7
    @6
    wceq
    wph
    @10
    wb
    #
    @0
    @3
    cA
    cB
    opeq12
    @14
    @6
    @7
    wph
    vx
    vy
    @6
    copsexg
    eqcoms
    syl
    copsex2g.1
    bitr3d
    exlimi
    exlimi
    sylbir
    syl2an
end
