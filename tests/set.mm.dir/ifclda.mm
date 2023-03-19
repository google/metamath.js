include "cif.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61dan.mm"

theorem ifclda
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume ifclda.1: |- ( ( ph /\ ps ) -> A e. C )
  assume ifclda.2: |- ( ( ph /\ -. ps ) -> B e. C )


  assert |- ( ph -> if ( ps , A , B ) e. C )

  proof
    wph
    wps
    wps
    cA
    cB
    cif
    #
    cC
    wcel
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
    ifclda.1
    eqeltrd
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
    ifclda.2
    eqeltrd
    pm2.61dan
end
