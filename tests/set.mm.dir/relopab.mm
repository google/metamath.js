include "copab.mm"
include "eqid.mm"
include "relopabi.mm"

theorem relopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- Rel { <. x , y >. | ph }

  proof
    wph
    vx
    vy
    wph
    vx
    vy
    copab
    #
    @0
    eqid
    relopabi
end
