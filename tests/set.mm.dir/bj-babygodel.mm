include "wfal.mm"
include "cprvb.mm"
include "wn.mm"
include "ax-prv1.mm"
include "biimpi.mm"
include "prvlem1.mm"
include "ax-prv3.mm"
include "pm2.21.mm"
include "prvlem2.mm"
include "sylc.mm"
include "con3i.mm"
include "sylibr.mm"
include "syl.mm"
include "mto.mm"
include "pm2.24ii.mm"

theorem bj-babygodel
  let wph: wff ph
  assume bj-babygodel.s: |- ( ph <-> -. Prv ph )
  assume bj-babygodel.1: |- -. Prv F.


  assert |- F.

  proof
    wfal
    cprvb
    #
    wn
    #
    cprvb
    #
    wfal
    @1
    bj-babygodel.1
    ax-prv1
    @2
    @0
    bj-babygodel.1
    @2
    wph
    cprvb
    #
    @0
    @1
    wph
    @1
    @3
    wn
    #
    wph
    @3
    @0
    @3
    @4
    cprvb
    @3
    cprvb
    @0
    wph
    @4
    wph
    @4
    bj-babygodel.s
    biimpi
    prvlem1
    wph
    ax-prv3
    @4
    @3
    wfal
    @3
    wfal
    pm2.21
    prvlem2
    sylc
    #
    con3i
    bj-babygodel.s
    sylibr
    prvlem1
    @5
    syl
    mto
    pm2.24ii
end
