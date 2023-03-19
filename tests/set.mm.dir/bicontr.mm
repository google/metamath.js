include "wn.mm"
include "wb.mm"
include "biid.mm"
include "notbinot1.mm"
include "mpbir.mm"
include "bifal.mm"

theorem bicontr
  let wph: wff ph


  assert |- ( ( -. ph <-> ph ) <-> F. )

  proof
    wph
    wn
    wph
    wb
    #
    @0
    wn
    wph
    wph
    wb
    wph
    biid
    wph
    wph
    notbinot1
    mpbir
    bifal
end
