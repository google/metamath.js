include "ccvs.mm"
include "wcel.mm"
include "clvec.mm"
include "cclm.mm"
include "df-cvs.mm"
include "elin2.mm"
include "simprbi.mm"
include "syl.mm"

theorem cvslvec
  let wph: wff ph
  let cW: class W
  assume cvslvec.1: |- ( ph -> W e. CVec )


  assert |- ( ph -> W e. LVec )

  proof
    wph
    cW
    ccvs
    wcel
    #
    cW
    clvec
    wcel
    #
    cvslvec.1
    @0
    cW
    cclm
    wcel
    @1
    cW
    cclm
    clvec
    ccvs
    df-cvs
    elin2
    simprbi
    syl
end
