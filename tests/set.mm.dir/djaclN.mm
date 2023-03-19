include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "co.mm"
include "cocaN.mm"
include "cfv.mm"
include "cin.mm"
include "crn.mm"
include "eqid.mm"
include "djavalN.mm"
include "inss1.mm"
include "docaclN.mm"
include "adantrr.mm"
include "diaelrnN.mm"
include "syldan.mm"
include "syl5ss.mm"
include "eqeltrd.mm"

theorem djaclN
  let cT: class T
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djacl.h: |- H = ( LHyp ` K )
  assume djacl.t: |- T = ( ( LTrn ` K ) ` W )
  assume djacl.i: |- I = ( ( DIsoA ` K ) ` W )
  assume djacl.j: |- J = ( ( vA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X C_ T /\ Y C_ T ) ) -> ( X J Y ) e. ran I )

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
    cT
    wss
    #
    cY
    cT
    wss
    #
    wa
    #
    wa
    #
    cX
    cY
    cJ
    co
    cX
    cW
    cK
    cocaN
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
    cT
    cH
    cI
    cJ
    cK
    @5
    cW
    cX
    cY
    djacl.h
    djacl.t
    djacl.i
    @5
    eqid
    #
    djacl.j
    djavalN
    @0
    @3
    @8
    cT
    wss
    @9
    @10
    wcel
    @4
    @8
    @6
    cT
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
    cT
    wss
    @0
    @1
    @12
    @2
    cT
    cH
    cI
    cK
    @5
    cW
    cX
    djacl.h
    djacl.t
    djacl.i
    @11
    docaclN
    adantrr
    @6
    cT
    cH
    cI
    cK
    chlt
    cW
    djacl.h
    djacl.t
    djacl.i
    diaelrnN
    syldan
    syl5ss
    cT
    cH
    cI
    cK
    @5
    cW
    @8
    djacl.h
    djacl.t
    djacl.i
    @11
    docaclN
    syldan
    eqeltrd
end
