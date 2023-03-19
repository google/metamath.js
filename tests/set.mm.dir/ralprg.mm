include "cpr.mm"
include "wral.mm"
include "csn.mm"
include "wa.mm"
include "wcel.mm"
include "cun.mm"
include "df-pr.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitri.mm"
include "ralsng.mm"
include "bi2anan9.mm"
include "syl5bb.mm"

theorem ralprg
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
  assert |- ( ( A e. V /\ B e. W ) -> ( A. x e. { A , B } ph <-> ( ps /\ ch ) ) )

  proof
    wph
    vx
    cA
    cB
    cpr
    #
    wral
    #
    wph
    vx
    cA
    csn
    #
    wral
    #
    wph
    vx
    cB
    csn
    #
    wral
    #
    wa
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
    wa
    @1
    wph
    vx
    @2
    @4
    cun
    #
    wral
    @6
    wph
    vx
    @0
    @9
    cA
    cB
    df-pr
    raleqi
    wph
    vx
    @2
    @4
    ralunb
    bitri
    @7
    @3
    wps
    @8
    @5
    wch
    wph
    wps
    vx
    cA
    cV
    ralprg.1
    ralsng
    wph
    wch
    vx
    cB
    cW
    ralprg.2
    ralsng
    bi2anan9
    syl5bb
end
