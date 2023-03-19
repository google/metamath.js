include "ccvs.mm"
include "wcel.mm"
include "cclm.mm"
include "clvec.mm"
include "df-cvs.mm"
include "elin2.mm"
include "simplbi.mm"
include "syl.mm"

theorem cvsclm
  let wph: wff ph
  let cW: class W
  assume cvslvec.1: |- ( ph -> W e. CVec )


  assert |- ( ph -> W e. CMod )

  proof
    wph
    cW
    ccvs
    wcel
    #
    cW
    cclm
    wcel
    #
    cvslvec.1
    @0
    @1
    cW
    clvec
    wcel
    cW
    cclm
    clvec
    ccvs
    df-cvs
    elin2
    simplbi
    syl
end
