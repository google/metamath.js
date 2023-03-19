include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtrd.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61dan.mm"

theorem ifeqda
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume ifeqda.1: |- ( ( ph /\ ps ) -> A = C )
  assume ifeqda.2: |- ( ( ph /\ -. ps ) -> B = C )


  assert |- ( ph -> if ( ps , A , B ) = C )

  proof
    wph
    wps
    wps
    cA
    cB
    cif
    #
    cC
    wceq
    wph
    wps
    wa
    @0
    cA
    cC
    wps
    @0
    cA
    wceq
    wph
    wps
    cA
    cB
    iftrue
    adantl
    ifeqda.1
    eqtrd
    wph
    wps
    wn
    #
    wa
    @0
    cB
    cC
    @1
    @0
    cB
    wceq
    wph
    wps
    cA
    cB
    iffalse
    adantl
    ifeqda.2
    eqtrd
    pm2.61dan
end
