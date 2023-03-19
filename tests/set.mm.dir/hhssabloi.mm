include "cva.mm"
include "cxp.mm"
include "cres.mm"
include "cgr.mm"
include "wcel.mm"
include "wss.mm"
include "hhssabloilem.mm"
include "simp2i.mm"
include "cdm.mm"
include "wceq.mm"
include "chil.mm"
include "shssii.mm"
include "xpss12.mm"
include "mp2an.mm"
include "ax-hfvadd.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "ssdmres.mm"
include "mpbi.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "sheli.mm"
include "ax-hvcom.mm"
include "syl2an.mm"
include "ovres.mm"
include "ancoms.mm"
include "3eqtr4d.mm"
include "isabloi.mm"

theorem hhssabloi
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hhssabl.1: |- H e. SH


  assert |- ( +h |` ( H X. H ) ) e. AbelOp

  proof
    vx
    vy
    cva
    cH
    cH
    cxp
    #
    cres
    #
    cH
    cva
    cgr
    wcel
    @1
    cgr
    wcel
    @1
    cva
    wss
    cH
    hhssabl.1
    hhssabloilem
    simp2i
    @0
    cva
    cdm
    #
    wss
    @1
    cdm
    @0
    wceq
    @0
    chil
    chil
    cxp
    #
    @2
    cH
    chil
    wss
    #
    @4
    @0
    @3
    wss
    cH
    hhssabl.1
    shssii
    #
    @5
    cH
    chil
    cH
    chil
    xpss12
    mp2an
    @3
    chil
    cva
    ax-hfvadd
    fdmi
    sseqtr4i
    @0
    cva
    ssdmres
    mpbi
    vx
    cv
    #
    cH
    wcel
    #
    vy
    cv
    #
    cH
    wcel
    #
    wa
    @6
    @8
    cva
    co
    #
    @8
    @6
    cva
    co
    #
    @6
    @8
    @1
    co
    @8
    @6
    @1
    co
    #
    @7
    @6
    chil
    wcel
    @8
    chil
    wcel
    @10
    @11
    wceq
    @9
    @6
    cH
    hhssabl.1
    sheli
    @8
    cH
    hhssabl.1
    sheli
    @6
    @8
    ax-hvcom
    syl2an
    @6
    @8
    cH
    cH
    cva
    ovres
    @9
    @7
    @12
    @11
    wceq
    @8
    @6
    cH
    cH
    cva
    ovres
    ancoms
    3eqtr4d
    isabloi
end
