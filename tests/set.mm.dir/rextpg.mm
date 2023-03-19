include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "wrex.mm"
include "csn.mm"
include "wo.mm"
include "ctp.mm"
include "w3o.mm"
include "wb.mm"
include "wa.mm"
include "rexprg.mm"
include "orbi1d.mm"
include "rexsng.mm"
include "orbi2d.mm"
include "sylan9bb.mm"
include "3impa.mm"
include "cun.mm"
include "df-tp.mm"
include "rexeqi.mm"
include "rexun.mm"
include "bitri.mm"
include "df-3or.mm"
include "3bitr4g.mm"

theorem rextpg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  assume ralprg.1: |- ( x = A -> ( ph <-> ps ) )
  assume ralprg.2: |- ( x = B -> ( ph <-> ch ) )
  assume raltpg.3: |- ( x = C -> ( ph <-> th ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ps x
  disjoint ch x
  disjoint th x
  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( E. x e. { A , B , C } ph <-> ( ps \/ ch \/ th ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    wph
    vx
    cA
    cB
    cpr
    #
    wrex
    #
    wph
    vx
    cC
    csn
    #
    wrex
    #
    wo
    #
    wps
    wch
    wo
    #
    wth
    wo
    #
    wph
    vx
    cA
    cB
    cC
    ctp
    #
    wrex
    #
    wps
    wch
    wth
    w3o
    @0
    @1
    @2
    @7
    @9
    wb
    @0
    @1
    wa
    #
    @7
    @8
    @6
    wo
    @2
    @9
    @12
    @4
    @8
    @6
    wph
    wps
    wch
    vx
    cA
    cB
    cV
    cW
    ralprg.1
    ralprg.2
    rexprg
    orbi1d
    @2
    @6
    wth
    @8
    wph
    wth
    vx
    cC
    cX
    raltpg.3
    rexsng
    orbi2d
    sylan9bb
    3impa
    @11
    wph
    vx
    @3
    @5
    cun
    #
    wrex
    @7
    wph
    vx
    @10
    @13
    cA
    cB
    cC
    df-tp
    rexeqi
    wph
    vx
    @3
    @5
    rexun
    bitri
    wps
    wch
    wth
    df-3or
    3bitr4g
end
