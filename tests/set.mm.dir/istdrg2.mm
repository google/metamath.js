include "ctdrg.mm"
include "wcel.mm"
include "ctrg.mm"
include "cdr.mm"
include "cui.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "ctgp.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "eqid.mm"
include "istdrg.mm"
include "wa.mm"
include "wceq.mm"
include "crg.mm"
include "isdrng.mm"
include "simprbi.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "pm5.32i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem istdrg2
  let cB: class B
  let cR: class R
  let cM: class M
  let c.0: class .0.
  assume istdrg2.m: |- M = ( mulGrp ` R )
  assume istdrg2.b: |- B = ( Base ` R )
  assume istdrg2.z: |- .0. = ( 0g ` R )


  assert |- ( R e. TopDRing <-> ( R e. TopRing /\ R e. DivRing /\ ( M |`s ( B \ { .0. } ) ) e. TopGrp ) )

  proof
    cR
    ctdrg
    wcel
    cR
    ctrg
    wcel
    #
    cR
    cdr
    wcel
    #
    cM
    cR
    cui
    cfv
    #
    cress
    co
    #
    ctgp
    wcel
    #
    w3a
    #
    @0
    @1
    cM
    cB
    c.0
    csn
    cdif
    #
    cress
    co
    #
    ctgp
    wcel
    #
    w3a
    #
    cR
    @2
    cM
    istdrg2.m
    @2
    eqid
    #
    istdrg
    @0
    @1
    wa
    #
    @4
    wa
    @11
    @8
    wa
    @5
    @9
    @11
    @4
    @8
    @11
    @3
    @7
    ctgp
    @11
    @2
    @6
    cM
    cress
    @1
    @2
    @6
    wceq
    #
    @0
    @1
    cR
    crg
    wcel
    @12
    cB
    cR
    @2
    c.0
    istdrg2.b
    @10
    istdrg2.z
    isdrng
    simprbi
    adantl
    oveq2d
    eleq1d
    pm5.32i
    @0
    @1
    @4
    df-3an
    @0
    @1
    @8
    df-3an
    3bitr4i
    bitri
end
