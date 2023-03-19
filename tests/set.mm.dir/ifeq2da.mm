include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "ifeq2d.mm"
include "pm2.61dan.mm"

theorem ifeq2da
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume ifeq2da.1: |- ( ( ph /\ -. ps ) -> A = B )


  assert |- ( ph -> if ( ps , C , A ) = if ( ps , C , B ) )

  proof
    wph
    wps
    wps
    cC
    cA
    cif
    #
    wps
    cC
    cB
    cif
    #
    wceq
    #
    wps
    @2
    wph
    wps
    @0
    cC
    @1
    wps
    cC
    cA
    iftrue
    wps
    cC
    cB
    iftrue
    eqtr4d
    adantl
    wph
    wps
    wn
    wa
    wps
    cA
    cB
    cC
    ifeq2da.1
    ifeq2d
    pm2.61dan
end
