include "wa.mm"
include "wn.mm"
include "wo.mm"
include "cif.mm"
include "wceq.mm"
include "pm3.13.mm"
include "iffalse.mm"
include "ifeq2d.mm"
include "eqtr4d.mm"
include "jaoi.mm"
include "syl.mm"

theorem ifcomnan
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( -. ( ph /\ ps ) -> if ( ph , A , if ( ps , B , C ) ) = if ( ps , B , if ( ph , A , C ) ) )

  proof
    wph
    wps
    wa
    wn
    wph
    wn
    #
    wps
    wn
    #
    wo
    wph
    cA
    wps
    cB
    cC
    cif
    #
    cif
    #
    wps
    cB
    wph
    cA
    cC
    cif
    #
    cif
    #
    wceq
    #
    wph
    wps
    pm3.13
    @0
    @6
    @1
    @0
    @3
    @2
    @5
    wph
    cA
    @2
    iffalse
    @0
    wps
    @4
    cC
    cB
    wph
    cA
    cC
    iffalse
    ifeq2d
    eqtr4d
    @1
    @3
    @4
    @5
    @1
    wph
    @2
    cC
    cA
    wps
    cB
    cC
    iffalse
    ifeq2d
    wps
    cB
    @4
    iffalse
    eqtr4d
    jaoi
    syl
end
