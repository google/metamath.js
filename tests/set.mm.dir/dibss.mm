include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cdia.mm"
include "cfv.mm"
include "cltrn.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "ctendo.mm"
include "wss.mm"
include "eqid.mm"
include "diass.mm"
include "tendo0cl.mm"
include "snssd.mm"
include "adantr.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "dibval2.mm"
include "wceq.mm"
include "dvhvbase.mm"
include "3sstr4d.mm"

theorem dibss
  let cB: class B
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  assume dibss.b: |- B = ( Base ` K )
  assume dibss.l: |- .<_ = ( le ` K )
  assume dibss.h: |- H = ( LHyp ` K )
  assume dibss.i: |- I = ( ( DIsoB ` K ) ` W )
  assume dibss.u: |- U = ( ( DVecH ` K ) ` W )
  assume dibss.v: |- V = ( Base ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( I ` X ) C_ V )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    #
    wa
    #
    cX
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    #
    vf
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cid
    cB
    cres
    cmpt
    #
    csn
    #
    cxp
    #
    @5
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cxp
    #
    cX
    cI
    cfv
    cV
    @2
    @4
    @5
    wss
    @7
    @9
    wss
    #
    @8
    @10
    wss
    cB
    @5
    cH
    @3
    cK
    c.le
    chlt
    cW
    cX
    dibss.b
    dibss.l
    dibss.h
    @5
    eqid
    #
    @3
    eqid
    #
    diass
    @0
    @11
    @1
    @0
    @6
    @9
    cB
    @5
    vf
    @9
    cH
    cK
    @6
    cW
    dibss.b
    dibss.h
    @12
    @9
    eqid
    #
    @6
    eqid
    #
    tendo0cl
    snssd
    adantr
    @4
    @5
    @7
    @9
    xpss12
    syl2anc
    cB
    @5
    vf
    cH
    cI
    @3
    cK
    c.le
    chlt
    cW
    cX
    @6
    dibss.b
    dibss.l
    dibss.h
    @12
    @15
    @13
    dibss.i
    dibval2
    @0
    cV
    @10
    wceq
    @1
    @5
    cU
    @9
    cH
    cK
    cV
    cW
    chlt
    dibss.h
    @12
    @14
    dibss.u
    dibss.v
    dvhvbase
    adantr
    3sstr4d
end
