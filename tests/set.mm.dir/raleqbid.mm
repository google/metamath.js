include "wral.mm"
include "wceq.mm"
include "wb.mm"
include "raleqf.mm"
include "syl.mm"
include "ralbid.mm"
include "bitrd.mm"

theorem raleqbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleqbid.0: |- F/ x ph
  assume raleqbid.1: |- F/_ x A
  assume raleqbid.2: |- F/_ x B
  assume raleqbid.3: |- ( ph -> A = B )
  assume raleqbid.4: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) )

  proof
    wph
    wps
    vx
    cA
    wral
    #
    wps
    vx
    cB
    wral
    #
    wch
    vx
    cB
    wral
    wph
    cA
    cB
    wceq
    @0
    @1
    wb
    raleqbid.3
    wps
    vx
    cA
    cB
    raleqbid.1
    raleqbid.2
    raleqf
    syl
    wph
    wps
    wch
    vx
    cB
    raleqbid.0
    raleqbid.4
    ralbid
    bitrd
end
