include "crngo.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cigen.mm"
include "co.mm"
include "wceq.mm"
include "cidl.mm"
include "cfv.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "igenidl.mm"
include "igenss.mm"
include "igenmin.mm"
include "3expia.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "3jca.mm"
include "eleq1.mm"
include "sseq2.mm"
include "sseq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "syl5ibcom.mm"
include "3adant3r3.mm"
include "adantlr.mm"
include "crab.mm"
include "cint.mm"
include "ssint.mm"
include "ralrab.mm"
include "sylbbr.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "igenval.mm"
include "sseqtr4d.mm"
include "eqssd.mm"
include "ex.mm"
include "impbid.mm"

theorem igenval2
  let cR: class R
  let cS: class S
  let vj: setvar j
  let cG: class G
  let cI: class I
  let cX: class X
  let vi: setvar i
  assume igenval2.1: |- G = ( 1st ` R )
  assume igenval2.2: |- X = ran G

  disjoint R j
  disjoint S j
  disjoint I j
  disjoint R i
  disjoint i j
  disjoint S i
  disjoint X i
  assert |- ( ( R e. RingOps /\ S C_ X ) -> ( ( R IdlGen S ) = I <-> ( I e. ( Idl ` R ) /\ S C_ I /\ A. j e. ( Idl ` R ) ( S C_ j -> I C_ j ) ) ) )

  proof
    cR
    crngo
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cR
    cS
    cigen
    co
    #
    cI
    wceq
    #
    cI
    cR
    cidl
    cfv
    #
    wcel
    #
    cS
    cI
    wss
    #
    cS
    vj
    cv
    #
    wss
    #
    cI
    @8
    wss
    #
    wi
    #
    vj
    @5
    wral
    #
    w3a
    #
    @2
    @3
    @5
    wcel
    #
    cS
    @3
    wss
    #
    @9
    @3
    @8
    wss
    #
    wi
    #
    vj
    @5
    wral
    #
    w3a
    @4
    @13
    @2
    @14
    @15
    @18
    cR
    cS
    cG
    cX
    igenval2.1
    igenval2.2
    igenidl
    cR
    cS
    cG
    cX
    igenval2.1
    igenval2.2
    igenss
    @0
    @18
    @1
    @0
    @17
    vj
    @5
    @0
    @8
    @5
    wcel
    @9
    @16
    cR
    cS
    @8
    igenmin
    3expia
    ralrimiva
    adantr
    3jca
    @4
    @14
    @6
    @15
    @7
    @18
    @12
    @3
    cI
    @5
    eleq1
    @3
    cI
    cS
    sseq2
    @4
    @17
    @11
    vj
    @5
    @4
    @16
    @10
    @9
    @3
    cI
    @8
    sseq1
    imbi2d
    ralbidv
    3anbi123d
    syl5ibcom
    @2
    @13
    @4
    @2
    @13
    wa
    #
    @3
    cI
    @0
    @13
    @3
    cI
    wss
    #
    @1
    @0
    @6
    @7
    @20
    @12
    cR
    cS
    cI
    igenmin
    3adant3r3
    adantlr
    @19
    cI
    cS
    vi
    cv
    #
    wss
    #
    vi
    @5
    crab
    #
    cint
    #
    @3
    @13
    cI
    @24
    wss
    #
    @2
    @12
    @6
    @25
    @7
    @25
    @10
    vj
    @23
    wral
    @12
    vj
    cI
    @23
    ssint
    @22
    @9
    @10
    vj
    vi
    @5
    @21
    @8
    cS
    sseq2
    ralrab
    sylbbr
    3ad2ant3
    adantl
    @2
    @3
    @24
    wceq
    @13
    cR
    cS
    vi
    cG
    cX
    igenval2.1
    igenval2.2
    igenval
    adantr
    sseqtr4d
    eqssd
    ex
    impbid
end
