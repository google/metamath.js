include "weu.mm"
include "cab.mm"
include "cio.mm"
include "csn.mm"
include "nfeu1.mm"
include "nfab1.mm"
include "nfiota1.mm"
include "nfsn.mm"
include "cv.mm"
include "wceq.mm"
include "wcel.mm"
include "iota1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "abid.mm"
include "velsn.mm"
include "3bitr4g.mm"
include "eqrd.mm"

theorem sniota
  let wph: wff ph
  let vx: setvar x


  assert |- ( E! x ph -> { x | ph } = { ( iota x ph ) } )

  proof
    wph
    vx
    weu
    #
    vx
    wph
    vx
    cab
    #
    wph
    vx
    cio
    #
    csn
    #
    wph
    vx
    nfeu1
    wph
    vx
    nfab1
    vx
    @2
    wph
    vx
    nfiota1
    nfsn
    @0
    wph
    vx
    cv
    #
    @2
    wceq
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    @0
    wph
    @2
    @4
    wceq
    @5
    wph
    vx
    iota1
    @2
    @4
    eqcom
    syl6bb
    wph
    vx
    abid
    vx
    @2
    velsn
    3bitr4g
    eqrd
end
