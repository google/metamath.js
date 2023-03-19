include "wa.mm"
include "wn.mm"
include "wo.mm"
include "exmid.mm"
include "ancli.mm"
include "pm4.42.mm"
include "ex.mm"
include "ancld.mm"
include "imp.mm"
include "orim12i.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "elim2if.mm"
include "mpbir.mm"

theorem elim2ifim
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
  assume elim2ifim.1: |- ( ph -> th )
  assume elim2ifim.2: |- ( ( -. ph /\ ps ) -> ta )
  assume elim2ifim.3: |- ( ( -. ph /\ -. ps ) -> et )


  assert |- ch

  proof
    wch
    wph
    wth
    wa
    #
    wph
    wn
    #
    wps
    wta
    wa
    #
    wps
    wn
    #
    wet
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wph
    @1
    wo
    @7
    wph
    exmid
    wph
    @0
    @1
    @6
    wph
    wth
    elim2ifim.1
    ancli
    @1
    @5
    @1
    @1
    wps
    wa
    #
    @1
    @3
    wa
    #
    wo
    @5
    @1
    wps
    pm4.42
    @8
    @2
    @9
    @4
    @1
    wps
    @2
    @1
    wps
    wta
    @1
    wps
    wta
    elim2ifim.2
    ex
    ancld
    imp
    @1
    @3
    @4
    @1
    @3
    wet
    @1
    @3
    wet
    elim2ifim.3
    ex
    ancld
    imp
    orim12i
    sylbi
    ancli
    orim12i
    ax-mp
    wph
    wps
    wch
    wth
    wta
    wet
    cA
    cB
    cC
    elim2if.1
    elim2if.2
    elim2if.3
    elim2if
    mpbir
end
