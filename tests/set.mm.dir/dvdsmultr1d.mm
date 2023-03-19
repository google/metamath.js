include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "wi.mm"
include "dvdsmultr1.mm"
include "syl3anc.mm"
include "mpd.mm"

theorem dvdsmultr1d
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cN: class N
  assume dvdsmultr1d.1: |- ( ph -> K e. ZZ )
  assume dvdsmultr1d.2: |- ( ph -> M e. ZZ )
  assume dvdsmultr1d.3: |- ( ph -> N e. ZZ )
  assume dvdsmultr1d.4: |- ( ph -> K || M )


  assert |- ( ph -> K || ( M x. N ) )

  proof
    wph
    cK
    cM
    cdvds
    wbr
    #
    cK
    cM
    cN
    cmul
    co
    cdvds
    wbr
    #
    dvdsmultr1d.4
    wph
    cK
    cz
    wcel
    cM
    cz
    wcel
    cN
    cz
    wcel
    @0
    @1
    wi
    dvdsmultr1d.1
    dvdsmultr1d.2
    dvdsmultr1d.3
    cK
    cM
    cN
    dvdsmultr1
    syl3anc
    mpd
end
