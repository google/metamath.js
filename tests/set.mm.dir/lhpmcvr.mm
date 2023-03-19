include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "cjn.mm"
include "cfv.mm"
include "cp1.mm"
include "eqid.mm"
include "lhp1cvr.mm"
include "adantr.mm"
include "lhpj1.mm"
include "breqtrrd.mm"
include "wb.mm"
include "simpll.mm"
include "cvrexch.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem lhpmcvr
  let cB: class B
  let cC: class C
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume lhpmcvr.b: |- B = ( Base ` K )
  assume lhpmcvr.l: |- .<_ = ( le ` K )
  assume lhpmcvr.m: |- ./\ = ( meet ` K )
  assume lhpmcvr.c: |- C = ( <o ` K )
  assume lhpmcvr.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) ) -> ( X ./\ W ) C X )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cX
    cW
    c.an
    co
    #
    cW
    cX
    c.an
    co
    #
    cX
    cC
    @6
    cK
    clat
    wcel
    #
    @3
    cW
    cB
    wcel
    #
    @7
    @8
    wceq
    @0
    @9
    @1
    @5
    cK
    hllat
    ad2antrr
    @2
    @3
    @4
    simprl
    #
    @1
    @10
    @0
    @5
    cB
    cH
    cK
    cW
    lhpmcvr.b
    lhpmcvr.h
    lhpbase
    ad2antlr
    #
    cB
    cK
    c.an
    cX
    cW
    lhpmcvr.b
    lhpmcvr.m
    latmcom
    syl3anc
    @6
    @8
    cX
    cC
    wbr
    #
    cW
    cW
    cX
    cK
    cjn
    cfv
    #
    co
    #
    cC
    wbr
    #
    @6
    cW
    cK
    cp1
    cfv
    #
    @15
    cC
    @2
    cW
    @17
    cC
    wbr
    @5
    chlt
    cC
    @17
    cH
    cK
    cW
    @17
    eqid
    #
    lhpmcvr.c
    lhpmcvr.h
    lhp1cvr
    adantr
    cB
    @17
    cH
    @14
    cK
    c.le
    cW
    cX
    lhpmcvr.b
    lhpmcvr.l
    @14
    eqid
    #
    @18
    lhpmcvr.h
    lhpj1
    breqtrrd
    @6
    @0
    @10
    @3
    @13
    @16
    wb
    @0
    @1
    @5
    simpll
    @12
    @11
    cB
    cC
    @14
    cK
    c.an
    cW
    cX
    lhpmcvr.b
    @19
    lhpmcvr.m
    lhpmcvr.c
    cvrexch
    syl3anc
    mpbird
    eqbrtrd
end
