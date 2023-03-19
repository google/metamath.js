include "wbr.mm"
include "cop.mm"
include "copab.mm"
include "wcel.mm"
include "wa.mm"
include "df-br.mm"
include "eleq2i.mm"
include "bitri.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "elopab.mm"
include "wb.mm"
include "elisset.mm"
include "eeanv.mm"
include "nfe1.mm"
include "nfbi.mm"
include "nfex.mm"
include "nfv.mm"
include "opeq12.mm"
include "copsexg.mm"
include "eqcoms.mm"
include "syl.mm"
include "bitr3d.mm"
include "exlimi.mm"
include "sylbir.mm"
include "syl2an.mm"
include "syl5bb.mm"

theorem brabgaf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W
  assume brabgaf.0: |- F/ x ps
  assume brabgaf.1: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )
  assume brabgaf.2: |- R = { <. x , y >. | ph }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps y
  assert |- ( ( A e. V /\ B e. W ) -> ( A R B <-> ps ) )

  proof
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cop
    #
    wph
    vx
    vy
    copab
    #
    wcel
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
    wps
    @0
    @1
    cR
    wcel
    @3
    cA
    cB
    cR
    df-br
    cR
    @2
    @1
    brabgaf.2
    eleq2i
    bitri
    @3
    @1
    vx
    cv
    #
    vy
    cv
    #
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
    @6
    wps
    wph
    vx
    vy
    @1
    elopab
    @4
    @7
    cA
    wceq
    #
    vx
    wex
    #
    @8
    cB
    wceq
    #
    vy
    wex
    #
    @12
    wps
    wb
    #
    @5
    vx
    cA
    cV
    elisset
    vy
    cB
    cW
    elisset
    @14
    @16
    wa
    @13
    @15
    wa
    #
    vy
    wex
    #
    vx
    wex
    @17
    @13
    @15
    vx
    vy
    eeanv
    @19
    @17
    vx
    @12
    wps
    vx
    @11
    vx
    nfe1
    brabgaf.0
    nfbi
    @18
    @17
    vy
    @12
    wps
    vy
    @11
    vy
    vx
    @10
    vy
    nfe1
    nfex
    wps
    vy
    nfv
    nfbi
    @18
    wph
    @12
    wps
    @18
    @9
    @1
    wceq
    wph
    @12
    wb
    #
    @7
    @8
    cA
    cB
    opeq12
    @20
    @1
    @9
    wph
    vx
    vy
    @1
    copsexg
    eqcoms
    syl
    brabgaf.1
    bitr3d
    exlimi
    exlimi
    sylbir
    syl2an
    syl5bb
    syl5bb
end
