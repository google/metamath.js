include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "3expa.mm"
include "iffalse.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "pm2.61dan.mm"

theorem 2if2
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume 2if2.1: |- ( ( ph /\ ps ) -> D = A )
  assume 2if2.2: |- ( ( ph /\ -. ps /\ th ) -> D = B )
  assume 2if2.3: |- ( ( ph /\ -. ps /\ -. th ) -> D = C )


  assert |- ( ph -> D = if ( ps , A , if ( th , B , C ) ) )

  proof
    wph
    wps
    cD
    wps
    cA
    wth
    cB
    cC
    cif
    #
    cif
    #
    wceq
    wph
    wps
    wa
    cD
    cA
    @1
    2if2.1
    wps
    @1
    cA
    wceq
    wph
    wps
    cA
    @0
    iftrue
    adantl
    eqtr4d
    wph
    wps
    wn
    #
    wa
    #
    cD
    @0
    @1
    @3
    wth
    cD
    @0
    wceq
    @3
    wth
    wa
    cD
    cB
    @0
    wph
    @2
    wth
    cD
    cB
    wceq
    2if2.2
    3expa
    wth
    @0
    cB
    wceq
    @3
    wth
    cB
    cC
    iftrue
    adantl
    eqtr4d
    @3
    wth
    wn
    #
    wa
    cD
    cC
    @0
    wph
    @2
    @4
    cD
    cC
    wceq
    2if2.3
    3expa
    @4
    cC
    @0
    wceq
    @3
    @4
    @0
    cC
    wth
    cB
    cC
    iffalse
    eqcomd
    adantl
    eqtrd
    pm2.61dan
    @2
    @1
    @0
    wceq
    wph
    wps
    cA
    @0
    iffalse
    adantl
    eqtr4d
    pm2.61dan
end
