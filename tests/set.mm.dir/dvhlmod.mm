include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "dvhlvec.mm"
include "lveclmod.mm"
include "syl.mm"

theorem dvhlmod
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  assume dvhlvec.h: |- H = ( LHyp ` K )
  assume dvhlvec.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhlvec.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> U e. LMod )

  proof
    wph
    cU
    clvec
    wcel
    cU
    clmod
    wcel
    wph
    cU
    cH
    cK
    cW
    dvhlvec.h
    dvhlvec.u
    dvhlvec.k
    dvhlvec
    cU
    lveclmod
    syl
end
