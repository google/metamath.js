include "copab.mm"
include "wfun.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wrel.mm"
include "relopab.mm"
include "nfopab1.mm"
include "nfopab2.mm"
include "dffun6f.mm"
include "mpbiran.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "opabid.mm"
include "bitri.mm"
include "mobii.mm"
include "albii.mm"

theorem funopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( Fun { <. x , y >. | ph } <-> A. x E* y ph )

  proof
    wph
    vx
    vy
    copab
    #
    wfun
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    #
    wph
    vy
    wmo
    #
    vx
    wal
    @1
    @0
    wrel
    @6
    wph
    vx
    vy
    relopab
    vx
    vy
    @0
    wph
    vx
    vy
    nfopab1
    wph
    vx
    vy
    nfopab2
    dffun6f
    mpbiran
    @5
    @7
    vx
    @4
    wph
    vy
    @4
    @2
    @3
    cop
    @0
    wcel
    wph
    @2
    @3
    @0
    df-br
    wph
    vx
    vy
    opabid
    bitri
    mobii
    albii
    bitri
end
