include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "crn.mm"
include "crest.mm"
include "co.mm"
include "cima.mm"
include "cfbas.mm"
include "cfv.mm"
include "uzrest.mm"
include "c0.mm"
include "wn.mm"
include "zfbas.mm"
include "0nelfb.mm"
include "ax-mp.mm"
include "imassrn.mm"
include "syl6eqss.mm"
include "sseld.mm"
include "mtoi.mm"
include "wss.mm"
include "wb.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "trfbas2.mm"
include "mp2an.mm"
include "sylibr.mm"
include "eqeltrrd.mm"

theorem uzfbas
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume uzfbas.1: |- Z = ( ZZ>= ` M )


  assert |- ( M e. ZZ -> ( ZZ>= " Z ) e. ( fBas ` Z ) )

  proof
    cM
    cz
    wcel
    #
    cuz
    crn
    #
    cZ
    crest
    co
    #
    cuz
    cZ
    cima
    #
    cZ
    cfbas
    cfv
    #
    cM
    cZ
    uzfbas.1
    uzrest
    #
    @0
    c0
    @2
    wcel
    #
    wn
    #
    @2
    @4
    wcel
    #
    @0
    @6
    c0
    @1
    wcel
    #
    @1
    cz
    cfbas
    cfv
    wcel
    #
    @9
    wn
    zfbas
    cz
    @1
    0nelfb
    ax-mp
    @0
    @2
    @1
    c0
    @0
    @2
    @3
    @1
    @5
    cuz
    cZ
    imassrn
    syl6eqss
    sseld
    mtoi
    @10
    cZ
    cz
    wss
    @8
    @7
    wb
    zfbas
    cZ
    cM
    cuz
    cfv
    cz
    uzfbas.1
    cM
    uzssz
    eqsstri
    cZ
    @1
    cz
    trfbas2
    mp2an
    sylibr
    eqeltrrd
end
