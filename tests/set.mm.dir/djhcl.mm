include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "co.mm"
include "coch.mm"
include "cfv.mm"
include "cin.mm"
include "crn.mm"
include "eqid.mm"
include "djhval.mm"
include "inss1.mm"
include "dochcl.mm"
include "adantrr.mm"
include "dihrnss.mm"
include "syldan.mm"
include "syl5ss.mm"
include "eqeltrd.mm"

theorem djhcl
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djhcl.h: |- H = ( LHyp ` K )
  assume djhcl.i: |- I = ( ( DIsoH ` K ) ` W )
  assume djhcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhcl.v: |- V = ( Base ` U )
  assume djhcl.j: |- .\/ = ( ( joinH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X C_ V /\ Y C_ V ) ) -> ( X .\/ Y ) e. ran I )

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
    cV
    wss
    #
    cY
    cV
    wss
    #
    wa
    #
    wa
    #
    cX
    cY
    c.or
    co
    cX
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    #
    cY
    @5
    cfv
    #
    cin
    #
    @5
    cfv
    #
    cI
    crn
    #
    cU
    cH
    c.or
    cK
    @5
    cV
    cW
    cX
    cY
    djhcl.h
    djhcl.u
    djhcl.v
    @5
    eqid
    #
    djhcl.j
    djhval
    @0
    @3
    @8
    cV
    wss
    @9
    @10
    wcel
    @4
    @8
    @6
    cV
    @6
    @7
    inss1
    @0
    @3
    @6
    @10
    wcel
    #
    @6
    cV
    wss
    @0
    @1
    @12
    @2
    cU
    cH
    cI
    cK
    @5
    cV
    cW
    cX
    djhcl.h
    djhcl.i
    djhcl.u
    djhcl.v
    @11
    dochcl
    adantrr
    cU
    cH
    cI
    cK
    cV
    cW
    @6
    djhcl.h
    djhcl.u
    djhcl.i
    djhcl.v
    dihrnss
    syldan
    syl5ss
    cU
    cH
    cI
    cK
    @5
    cV
    cW
    @8
    djhcl.h
    djhcl.i
    djhcl.u
    djhcl.v
    @11
    dochcl
    syldan
    eqeltrd
end
