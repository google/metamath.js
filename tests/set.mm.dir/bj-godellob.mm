include "wfal.mm"
include "cprvb.mm"
include "wn.mm"
include "wi.mm"
include "dfnot.mm"
include "bitri.mm"
include "pm2.21i.mm"
include "bj-babylob.mm"

theorem bj-godellob
  let wph: wff ph
  assume bj-godellob.s: |- ( ph <-> -. Prv ph )
  assume bj-godellob.1: |- -. Prv F.


  assert |- F.

  proof
    wfal
    wph
    wph
    wph
    cprvb
    #
    wn
    @0
    wfal
    wi
    bj-godellob.s
    @0
    dfnot
    bitri
    wfal
    cprvb
    wfal
    bj-godellob.1
    pm2.21i
    bj-babylob
end
