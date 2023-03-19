include "cdiv.mm"
include "cdm.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cxp.mm"
include "wceq.mm"
include "c1.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "c0.mm"
include "cv.mm"
include "cmul.mm"
include "crio.mm"
include "df-div.mm"
include "riotaex.mm"
include "dmmpt2.mm"
include "eqid.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "necon2bi.mm"
include "ax-mp.mm"
include "ndmovg.mm"
include "mp2an.mm"

theorem 1div0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( 1 / 0 ) = (/)

  proof
    cdiv
    cdm
    cc
    cc
    cc0
    csn
    cdif
    #
    cxp
    wceq
    c1
    cc
    wcel
    #
    cc0
    @0
    wcel
    #
    wa
    #
    wn
    #
    c1
    cc0
    cdiv
    co
    c0
    wceq
    vx
    vy
    cc
    @0
    vy
    cv
    vz
    cv
    cmul
    co
    vx
    cv
    wceq
    #
    vz
    cc
    crio
    cdiv
    vx
    vy
    vz
    df-div
    @5
    vz
    cc
    riotaex
    dmmpt2
    cc0
    cc0
    wceq
    @4
    cc0
    eqid
    @3
    cc0
    cc0
    @2
    cc0
    cc0
    wne
    @1
    cc0
    cc
    cc0
    eldifsni
    adantl
    necon2bi
    ax-mp
    c1
    cc0
    cc
    @0
    cdiv
    ndmovg
    mp2an
end
