include "codd.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cz.mm"
include "wcel.mm"
include "crab.mm"
include "cmo.mm"
include "wceq.mm"
include "dfodd2.mm"
include "cc0.mm"
include "cr.mm"
include "crp.mm"
include "wb.mm"
include "peano2zm.mm"
include "zred.mm"
include "2rp.mm"
include "mod0.mm"
include "sylancl.mm"
include "clt.mm"
include "wbr.mm"
include "zre.mm"
include "2re.mm"
include "a1i.mm"
include "1lt2.mm"
include "m1mod0mod1.mm"
include "syl3anc.mm"
include "bitr3d.mm"
include "rabbiia.mm"
include "eqtri.mm"

theorem dfodd4
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x


  assert |- Odd = { z e. ZZ | ( z mod 2 ) = 1 }

  proof
    codd
    vz
    cv
    #
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    cz
    wcel
    #
    vz
    cz
    crab
    @0
    c2
    cmo
    co
    c1
    wceq
    #
    vz
    cz
    crab
    vz
    dfodd2
    @2
    @3
    vz
    cz
    @0
    cz
    wcel
    #
    @1
    c2
    cmo
    co
    cc0
    wceq
    #
    @2
    @3
    @4
    @1
    cr
    wcel
    c2
    crp
    wcel
    @5
    @2
    wb
    @4
    @1
    @0
    peano2zm
    zred
    2rp
    @1
    c2
    mod0
    sylancl
    @4
    @0
    cr
    wcel
    c2
    cr
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    @5
    @3
    wb
    @0
    zre
    @6
    @4
    2re
    a1i
    @7
    @4
    1lt2
    a1i
    @0
    c2
    m1mod0mod1
    syl3anc
    bitr3d
    rabbiia
    eqtri
end
