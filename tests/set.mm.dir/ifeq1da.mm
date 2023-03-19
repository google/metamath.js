include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "ifeq1d.mm"
include "wn.mm"
include "iffalse.mm"
include "eqtr4d.mm"
include "adantl.mm"
include "pm2.61dan.mm"

theorem ifeq1da
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume ifeq1da.1: |- ( ( ph /\ ps ) -> A = B )


  assert |- ( ph -> if ( ps , A , C ) = if ( ps , B , C ) )

  proof
    wph
    wps
    wps
    cA
    cC
    cif
    #
    wps
    cB
    cC
    cif
    #
    wceq
    #
    wph
    wps
    wa
    wps
    cA
    cB
    cC
    ifeq1da.1
    ifeq1d
    wps
    wn
    #
    @2
    wph
    @3
    @0
    cC
    @1
    wps
    cA
    cC
    iffalse
    wps
    cB
    cC
    iffalse
    eqtr4d
    adantl
    pm2.61dan
end
