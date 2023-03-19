include "wa.mm"
include "wn.mm"
include "wo.mm"
include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "iftrue.mm"
include "syl.mm"
include "iffalse.mm"
include "eqeq1d.mm"
include "syl6bir.mm"
include "elimifd.mm"
include "cases.mm"

theorem elim2if
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let cA: class A
  let cB: class B
  let cC: class C
  assume elim2if.1: |- ( if ( ph , A , if ( ps , B , C ) ) = A -> ( ch <-> th ) )
  assume elim2if.2: |- ( if ( ph , A , if ( ps , B , C ) ) = B -> ( ch <-> ta ) )
  assume elim2if.3: |- ( if ( ph , A , if ( ps , B , C ) ) = C -> ( ch <-> et ) )


  assert |- ( ch <-> ( ( ph /\ th ) \/ ( -. ph /\ ( ( ps /\ ta ) \/ ( -. ps /\ et ) ) ) ) )

  proof
    wph
    wch
    wth
    wps
    wta
    wa
    wps
    wn
    wet
    wa
    wo
    wph
    wph
    cA
    wps
    cB
    cC
    cif
    #
    cif
    #
    cA
    wceq
    wch
    wth
    wb
    wph
    cA
    @0
    iftrue
    elim2if.1
    syl
    wph
    wn
    #
    wps
    wch
    wta
    wet
    cB
    cC
    @2
    @0
    cB
    wceq
    @1
    cB
    wceq
    wch
    wta
    wb
    @2
    @1
    @0
    cB
    wph
    cA
    @0
    iffalse
    #
    eqeq1d
    elim2if.2
    syl6bir
    @2
    @0
    cC
    wceq
    @1
    cC
    wceq
    wch
    wet
    wb
    @2
    @1
    @0
    cC
    @3
    eqeq1d
    elim2if.3
    syl6bir
    elimifd
    cases
end
