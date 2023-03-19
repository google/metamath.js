include "c1.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cdiv.mm"
include "halfnz.mm"
include "eleq1a.mm"
include "mtoi.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "1cnd.mm"
include "zcn.mm"
include "2cnne0.mm"
include "a1i.mm"
include "divmul2.mm"
include "syl3anc.mm"
include "mtbid.mm"
include "nrex.mm"
include "intnan.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "mtbir.mm"
include "nelir.mm"

theorem 1neven
  let vx: setvar x
  let vz: setvar z
  let cE: class E
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }

  disjoint x z
  disjoint k x
  assert |- 1 e/ E

  proof
    c1
    cE
    c1
    cE
    wcel
    c1
    cz
    wcel
    #
    c1
    c2
    vx
    cv
    #
    cmul
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    @4
    @0
    @3
    vx
    cz
    @1
    cz
    wcel
    #
    c1
    c2
    cdiv
    co
    #
    @1
    wceq
    #
    @3
    @5
    @7
    @6
    cz
    wcel
    halfnz
    @1
    cz
    @6
    eleq1a
    mtoi
    @5
    c1
    cc
    wcel
    @1
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    #
    @7
    @3
    wb
    @5
    1cnd
    @1
    zcn
    @8
    @5
    2cnne0
    a1i
    c1
    @1
    c2
    divmul2
    syl3anc
    mtbid
    nrex
    intnan
    vz
    cv
    #
    @2
    wceq
    #
    vx
    cz
    wrex
    @4
    vz
    c1
    cz
    cE
    @9
    c1
    wceq
    @10
    @3
    vx
    cz
    @9
    c1
    @2
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    mtbir
    nelir
end
