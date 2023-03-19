include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "wral.mm"
include "csn.mm"
include "wa.mm"
include "ctp.mm"
include "wb.mm"
include "ralprg.mm"
include "ralsng.mm"
include "bi2anan9.mm"
include "3impa.mm"
include "cun.mm"
include "df-tp.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitri.mm"
include "df-3an.mm"
include "3bitr4g.mm"

theorem raltpg
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
  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( A. x e. { A , B , C } ph <-> ( ps /\ ch /\ th ) ) )

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
    wral
    #
    wph
    vx
    cC
    csn
    #
    wral
    #
    wa
    #
    wps
    wch
    wa
    #
    wth
    wa
    #
    wph
    vx
    cA
    cB
    cC
    ctp
    #
    wral
    #
    wps
    wch
    wth
    w3a
    @0
    @1
    @2
    @7
    @9
    wb
    @0
    @1
    wa
    @4
    @8
    @2
    @6
    wth
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
    ralprg
    wph
    wth
    vx
    cC
    cX
    raltpg.3
    ralsng
    bi2anan9
    3impa
    @11
    wph
    vx
    @3
    @5
    cun
    #
    wral
    @7
    wph
    vx
    @10
    @12
    cA
    cB
    cC
    df-tp
    raleqi
    wph
    vx
    @3
    @5
    ralunb
    bitri
    wps
    wch
    wth
    df-3an
    3bitr4g
end
