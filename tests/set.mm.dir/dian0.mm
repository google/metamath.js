include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cid.mm"
include "cres.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cltrn.mm"
include "ctrl.mm"
include "eqid.mm"
include "idltrn.mm"
include "adantr.mm"
include "cp0.mm"
include "wceq.mm"
include "trlid0.mm"
include "cal.mm"
include "hlatl.mm"
include "simpl.mm"
include "atl0le.mm"
include "syl2an.mm"
include "eqbrtrd.mm"
include "diaelval.mm"
include "mpbir2and.mm"
include "ne0i.mm"
include "syl.mm"

theorem dian0
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  assume dian0.b: |- B = ( Base ` K )
  assume dian0.l: |- .<_ = ( le ` K )
  assume dian0.h: |- H = ( LHyp ` K )
  assume dian0.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( I ` X ) =/= (/) )

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
    #
    wa
    #
    wa
    #
    cid
    cB
    cres
    #
    cX
    cI
    cfv
    #
    wcel
    #
    @8
    c0
    wne
    @6
    @9
    @7
    cW
    cK
    cltrn
    cfv
    cfv
    #
    wcel
    #
    @7
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    cX
    c.le
    wbr
    @2
    @11
    @5
    cB
    @10
    cH
    cK
    cW
    dian0.b
    dian0.h
    @10
    eqid
    #
    idltrn
    adantr
    @6
    @13
    cK
    cp0
    cfv
    #
    cX
    c.le
    @2
    @13
    @15
    wceq
    @5
    cB
    @12
    cH
    cK
    cW
    @15
    dian0.b
    @15
    eqid
    #
    dian0.h
    @12
    eqid
    #
    trlid0
    adantr
    @2
    cK
    cal
    wcel
    #
    @3
    @15
    cX
    c.le
    wbr
    @5
    @0
    @18
    @1
    cK
    hlatl
    adantr
    @3
    @4
    simpl
    cB
    cK
    c.le
    cX
    @15
    dian0.b
    dian0.l
    @16
    atl0le
    syl2an
    eqbrtrd
    cB
    @12
    @10
    @7
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dian0.b
    dian0.l
    dian0.h
    @14
    @17
    dian0.i
    diaelval
    mpbir2and
    @8
    @7
    ne0i
    syl
end
