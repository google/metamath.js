include "cprvb.mm"
include "wi.mm"
include "ax-prv3.mm"
include "biimpi.mm"
include "prvlem2.mm"
include "mpd.mm"
include "syl.mm"
include "mpbir.mm"
include "ax-prv1.mm"
include "ax-mp.mm"

theorem bj-babylob
  let wph: wff ph
  let wps: wff ps
  assume bj-babylob.s: |- ( ps <-> ( Prv ps -> ph ) )
  assume bj-babylob.1: |- ( Prv ph -> ph )


  assert |- ph

  proof
    wps
    cprvb
    #
    wph
    wps
    wps
    @0
    wph
    wi
    #
    @0
    wph
    cprvb
    #
    wph
    @0
    @0
    cprvb
    @2
    wps
    ax-prv3
    wps
    @0
    wph
    wps
    @1
    bj-babylob.s
    biimpi
    prvlem2
    mpd
    bj-babylob.1
    syl
    #
    bj-babylob.s
    mpbir
    ax-prv1
    @3
    ax-mp
end
