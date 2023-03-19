include "cdvds.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "dvds2sub.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem dvds2subd
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume dvds2subd.1: |- ( ph -> K e. ZZ )
  assume dvds2subd.2: |- ( ph -> K || M )
  assume dvds2subd.3: |- ( ph -> K || N )
  assume dvds2subd.4: |- ( ph -> M e. ZZ )
  assume dvds2subd.5: |- ( ph -> N e. ZZ )


  assert |- ( ph -> K || ( M - N ) )

  proof
    wph
    cK
    cM
    cdvds
    wbr
    #
    cK
    cN
    cdvds
    wbr
    #
    cK
    cM
    cN
    cmin
    co
    cdvds
    wbr
    #
    dvds2subd.2
    dvds2subd.3
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
    wa
    @2
    wi
    dvds2subd.1
    dvds2subd.4
    dvds2subd.5
    cK
    cM
    cN
    dvds2sub
    syl3anc
    mp2and
end
