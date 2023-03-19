include "cif.mm"
include "wceq.mm"
include "ifeq1da.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "sylan9eq.mm"
include "wn.mm"
include "ifeq2da.mm"
include "iffalse.mm"
include "pm2.61dan.mm"

theorem ifeq12da
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ifeq12da.1: |- ( ( ph /\ ps ) -> A = C )
  assume ifeq12da.2: |- ( ( ph /\ -. ps ) -> B = D )


  assert |- ( ph -> if ( ps , A , B ) = if ( ps , C , D ) )

  proof
    wph
    wps
    wps
    cA
    cB
    cif
    #
    wps
    cC
    cD
    cif
    #
    wceq
    wph
    wps
    @0
    wps
    cC
    cB
    cif
    #
    @1
    wph
    wps
    cA
    cC
    cB
    ifeq12da.1
    ifeq1da
    wps
    @2
    cC
    @1
    wps
    cC
    cB
    iftrue
    wps
    cC
    cD
    iftrue
    eqtr4d
    sylan9eq
    wph
    wps
    wn
    #
    @0
    wps
    cA
    cD
    cif
    #
    @1
    wph
    wps
    cB
    cD
    cA
    ifeq12da.2
    ifeq2da
    @3
    @4
    cD
    @1
    wps
    cA
    cD
    iffalse
    wps
    cC
    cD
    iffalse
    eqtr4d
    sylan9eq
    pm2.61dan
end
