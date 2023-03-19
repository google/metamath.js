include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cbs.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "ctendo.mm"
include "eqid.mm"
include "tendoidcl.mm"
include "erngbase.mm"
include "eleqtrrd.mm"
include "cmpt.mm"
include "tendo1ne0.mm"
include "erng0g.mm"
include "neeqtrrd.mm"
include "ccom.mm"
include "id.mm"
include "erngmul.mm"
include "syl12anc.mm"
include "wf1o.mm"
include "wf.mm"
include "f1oi.mm"
include "f1of.mm"
include "fcoi2.mm"
include "mp2b.mm"
include "syl6eq.mm"
include "3jca.mm"
include "cdr.mm"
include "wb.mm"
include "erngdv.mm"
include "drngid2.mm"
include "syl.mm"
include "mpbid.mm"

theorem erng1r
  let cD: class D
  let cT: class T
  let c.1: class .1.
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  assume erng1r.h: |- H = ( LHyp ` K )
  assume erng1r.t: |- T = ( ( LTrn ` K ) ` W )
  assume erng1r.d: |- D = ( ( EDRing ` K ) ` W )
  assume erng1r.r: |- .1. = ( 1r ` D )


  assert |- ( ( K e. HL /\ W e. H ) -> .1. = ( _I |` T ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cid
    cT
    cres
    #
    cD
    cbs
    cfv
    #
    wcel
    #
    @1
    cD
    c0g
    cfv
    #
    wne
    #
    @1
    @1
    cD
    cmulr
    cfv
    #
    co
    #
    @1
    wceq
    #
    w3a
    #
    c.1
    @1
    wceq
    #
    @0
    @3
    @5
    @8
    @0
    @1
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @2
    cT
    @11
    cH
    cK
    cW
    erng1r.h
    erng1r.t
    @11
    eqid
    #
    tendoidcl
    #
    @2
    cD
    cT
    @11
    cH
    cK
    chlt
    cW
    erng1r.h
    erng1r.t
    @12
    erng1r.d
    @2
    eqid
    #
    erngbase
    eleqtrrd
    @0
    @1
    vf
    cT
    cid
    cK
    cbs
    cfv
    #
    cres
    cmpt
    #
    @4
    @15
    cT
    vf
    @11
    cH
    cK
    @16
    cW
    @15
    eqid
    #
    erng1r.h
    erng1r.t
    @12
    @16
    eqid
    #
    tendo1ne0
    @15
    cD
    cT
    vf
    cH
    cK
    @16
    cW
    @4
    @17
    erng1r.h
    erng1r.t
    erng1r.d
    @18
    @4
    eqid
    #
    erng0g
    neeqtrrd
    @0
    @7
    @1
    @1
    ccom
    #
    @1
    @0
    @0
    @1
    @11
    wcel
    #
    @21
    @7
    @20
    wceq
    @0
    id
    @13
    @13
    cD
    cT
    @6
    @1
    @11
    cH
    cK
    @1
    cW
    chlt
    erng1r.h
    erng1r.t
    @12
    erng1r.d
    @6
    eqid
    #
    erngmul
    syl12anc
    cT
    cT
    @1
    wf1o
    cT
    cT
    @1
    wf
    @20
    @1
    wceq
    cT
    f1oi
    cT
    cT
    @1
    f1of
    cT
    cT
    @1
    fcoi2
    mp2b
    syl6eq
    3jca
    @0
    cD
    cdr
    wcel
    @9
    @10
    wb
    cD
    cH
    cK
    cW
    erng1r.h
    erng1r.d
    erngdv
    @2
    cD
    @6
    c.1
    @1
    @4
    @14
    @22
    @19
    erng1r.r
    drngid2
    syl
    mpbid
end
