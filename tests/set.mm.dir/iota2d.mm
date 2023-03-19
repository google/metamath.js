include "nfv.mm"
include "nfvd.mm"
include "nfcvd.mm"
include "iota2df.mm"

theorem iota2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cB: class B
  let cV: class V
  assume iota2df.1: |- ( ph -> B e. V )
  assume iota2df.2: |- ( ph -> E! x ps )
  assume iota2df.3: |- ( ( ph /\ x = B ) -> ( ps <-> ch ) )

  disjoint B x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( ch <-> ( iota x ps ) = B ) )

  proof
    wph
    wps
    wch
    vx
    cB
    cV
    iota2df.1
    iota2df.2
    iota2df.3
    wph
    vx
    nfv
    wph
    wch
    vx
    nfvd
    wph
    vx
    cB
    nfcvd
    iota2df
end
