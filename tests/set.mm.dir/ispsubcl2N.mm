include "chlt.mm"
include "wcel.mm"
include "catm.mm"
include "cfv.mm"
include "wss.mm"
include "cpolN.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "eqid.mm"
include "ispsubclN.mm"
include "club.mm"
include "coc.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "ccla.mm"
include "hlclat.mm"
include "polssatN.mm"
include "atssbase.mm"
include "syl6ss.mm"
include "clatlubcl.mm"
include "syl2anc.mm"
include "opoccl.mm"
include "ex.mm"
include "adantrd.mm"
include "wi.mm"
include "polval2N.mm"
include "syldan.mm"
include "eqeq1.mm"
include "biimpcd.mm"
include "syl6.mm"
include "impd.mm"
include "jcad.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "pmapssat.mm"
include "2polpmapN.mm"
include "sseq1.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "biimprcd.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "bitrd.mm"

theorem ispsubcl2N
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cK: class K
  let cM: class M
  let cX: class X
  assume pmapsubcl.b: |- B = ( Base ` K )
  assume pmapsubcl.m: |- M = ( pmap ` K )
  assume pmapsubcl.c: |- C = ( PSubCl ` K )

  disjoint B y
  disjoint K y
  disjoint M y
  disjoint X y
  assert |- ( K e. HL -> ( X e. C <-> E. y e. B X = ( M ` y ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cC
    wcel
    cX
    cK
    catm
    cfv
    #
    wss
    #
    cX
    cK
    cpolN
    cfv
    #
    cfv
    #
    @3
    cfv
    #
    cX
    wceq
    #
    wa
    #
    cX
    vy
    cv
    #
    cM
    cfv
    #
    wceq
    #
    vy
    cB
    wrex
    #
    @1
    cC
    chlt
    cK
    @3
    cX
    @1
    eqid
    #
    @3
    eqid
    #
    pmapsubcl.c
    ispsubclN
    @0
    @7
    @11
    @0
    @7
    @4
    cK
    club
    cfv
    #
    cfv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    cB
    wcel
    #
    cX
    @17
    cM
    cfv
    #
    wceq
    #
    wa
    @11
    @0
    @7
    @18
    @20
    @0
    @2
    @18
    @6
    @0
    @2
    @18
    @0
    @2
    wa
    #
    cK
    cops
    wcel
    #
    @15
    cB
    wcel
    #
    @18
    @0
    @22
    @2
    cK
    hlop
    adantr
    @21
    cK
    ccla
    wcel
    #
    @4
    cB
    wss
    @23
    @0
    @24
    @2
    cK
    hlclat
    adantr
    @21
    @4
    @1
    cB
    @1
    cK
    @3
    cX
    @12
    @13
    polssatN
    #
    @1
    cB
    cK
    pmapsubcl.b
    @12
    atssbase
    syl6ss
    cB
    @4
    @14
    cK
    pmapsubcl.b
    @14
    eqid
    #
    clatlubcl
    syl2anc
    cB
    cK
    @16
    @15
    pmapsubcl.b
    @16
    eqid
    #
    opoccl
    syl2anc
    ex
    adantrd
    @0
    @2
    @6
    @20
    @0
    @2
    @5
    @19
    wceq
    #
    @6
    @20
    wi
    @0
    @2
    @28
    @0
    @2
    @4
    @1
    wss
    @28
    @25
    @1
    @3
    @14
    cK
    cM
    @16
    @4
    @26
    @27
    @12
    pmapsubcl.m
    @13
    polval2N
    syldan
    ex
    @6
    @28
    @20
    @5
    cX
    @19
    eqeq1
    biimpcd
    syl6
    impd
    jcad
    @10
    @20
    vy
    @17
    cB
    @8
    @17
    wceq
    @9
    @19
    cX
    @8
    @17
    cM
    fveq2
    eqeq2d
    rspcev
    syl6
    @0
    @10
    @7
    vy
    cB
    @0
    @8
    cB
    wcel
    wa
    @9
    @1
    wss
    #
    @9
    @3
    cfv
    #
    @3
    cfv
    #
    @9
    wceq
    #
    @10
    @7
    wi
    @1
    cB
    chlt
    cK
    cM
    @8
    pmapsubcl.b
    @12
    pmapsubcl.m
    pmapssat
    cB
    cK
    cM
    @3
    @8
    pmapsubcl.b
    pmapsubcl.m
    @13
    2polpmapN
    @10
    @7
    @29
    @32
    wa
    @10
    @2
    @29
    @6
    @32
    cX
    @9
    @1
    sseq1
    @10
    @5
    @31
    cX
    @9
    @10
    @4
    @30
    @3
    cX
    @9
    @3
    fveq2
    fveq2d
    @10
    id
    eqeq12d
    anbi12d
    biimprcd
    syl2anc
    rexlimdva
    impbid
    bitrd
end
