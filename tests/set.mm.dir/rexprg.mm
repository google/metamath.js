include "cpr.mm"
include "wrex.mm"
include "csn.mm"
include "wo.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "df-pr.mm"
include "rexeqi.mm"
include "rexun.mm"
include "bitri.mm"
include "rexsng.mm"
include "orbi1d.mm"
include "orbi2d.mm"
include "sylan9bb.mm"
include "syl5bb.mm"

theorem rexprg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let cC: class C
  let wth: wff th
  assume ralprg.1: |- ( x = A -> ( ph <-> ps ) )
  assume ralprg.2: |- ( x = B -> ( ph <-> ch ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  disjoint ch x
  disjoint C x
  disjoint th x
  assert |- ( ( A e. V /\ B e. W ) -> ( E. x e. { A , B } ph <-> ( ps \/ ch ) ) )

  proof
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
    cA
    csn
    #
    wrex
    #
    wph
    vx
    cB
    csn
    #
    wrex
    #
    wo
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
    wps
    wch
    wo
    #
    @1
    wph
    vx
    @2
    @4
    cun
    #
    wrex
    @6
    wph
    vx
    @0
    @10
    cA
    cB
    df-pr
    rexeqi
    wph
    vx
    @2
    @4
    rexun
    bitri
    @7
    @6
    wps
    @5
    wo
    @8
    @9
    @7
    @3
    wps
    @5
    wph
    wps
    vx
    cA
    cV
    ralprg.1
    rexsng
    orbi1d
    @8
    @5
    wch
    wps
    wph
    wch
    vx
    cB
    cW
    ralprg.2
    rexsng
    orbi2d
    sylan9bb
    syl5bb
end
