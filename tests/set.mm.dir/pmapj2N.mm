include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "coc.mm"
include "cfv.mm"
include "cmee.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "clat.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "cops.mm"
include "hlop.mm"
include "simp2.mm"
include "eqid.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "polpmapN.mm"
include "cin.mm"
include "3adant3.mm"
include "3adant2.mm"
include "ineq12d.mm"
include "catm.mm"
include "wss.mm"
include "pmapssat.mm"
include "poldmj1N.mm"
include "pmapmeet.mm"
include "3eqtr4rd.mm"
include "fveq2d.mm"
include "col.mm"
include "hlol.mm"
include "oldmm4.mm"
include "syl3an1.mm"
include "3eqtr3rd.mm"

theorem pmapj2N
  let cB: class B
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume pmapj2.b: |- B = ( Base ` K )
  assume pmapj2.j: |- .\/ = ( join ` K )
  assume pmapj2.m: |- M = ( pmap ` K )
  assume pmapj2.p: |- .+ = ( +P ` K )
  assume pmapj2.o: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( M ` ( X .\/ Y ) ) = ( ._|_ ` ( ._|_ ` ( ( M ` X ) .+ ( M ` Y ) ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cK
    coc
    cfv
    #
    cfv
    #
    cY
    @4
    cfv
    #
    cK
    cmee
    cfv
    #
    co
    #
    cM
    cfv
    #
    c.pe
    cfv
    #
    @8
    @4
    cfv
    #
    cM
    cfv
    #
    cX
    cM
    cfv
    #
    cY
    cM
    cfv
    #
    c.pl
    co
    c.pe
    cfv
    #
    c.pe
    cfv
    cX
    cY
    c.or
    co
    #
    cM
    cfv
    @3
    @0
    @8
    cB
    wcel
    #
    @10
    @12
    wceq
    @0
    @1
    @2
    simp1
    #
    @3
    cK
    clat
    wcel
    #
    @5
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    @17
    @0
    @1
    @19
    @2
    cK
    hllat
    3ad2ant1
    @3
    cK
    cops
    wcel
    #
    @1
    @20
    @0
    @1
    @22
    @2
    cK
    hlop
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    cB
    cK
    @4
    cX
    pmapj2.b
    @4
    eqid
    #
    opoccl
    syl2anc
    #
    @3
    @22
    @2
    @21
    @23
    @0
    @1
    @2
    simp3
    cB
    cK
    @4
    cY
    pmapj2.b
    @24
    opoccl
    syl2anc
    #
    cB
    cK
    @7
    @5
    @6
    pmapj2.b
    @7
    eqid
    #
    latmcl
    syl3anc
    cB
    c.pe
    cK
    cM
    @4
    @8
    pmapj2.b
    @24
    pmapj2.m
    pmapj2.o
    polpmapN
    syl2anc
    @3
    @9
    @15
    c.pe
    @3
    @13
    c.pe
    cfv
    #
    @14
    c.pe
    cfv
    #
    cin
    #
    @5
    cM
    cfv
    #
    @6
    cM
    cfv
    #
    cin
    #
    @15
    @9
    @3
    @28
    @31
    @29
    @32
    @0
    @1
    @28
    @31
    wceq
    @2
    cB
    c.pe
    cK
    cM
    @4
    cX
    pmapj2.b
    @24
    pmapj2.m
    pmapj2.o
    polpmapN
    3adant3
    @0
    @2
    @29
    @32
    wceq
    @1
    cB
    c.pe
    cK
    cM
    @4
    cY
    pmapj2.b
    @24
    pmapj2.m
    pmapj2.o
    polpmapN
    3adant2
    ineq12d
    @3
    @0
    @13
    cK
    catm
    cfv
    #
    wss
    #
    @14
    @34
    wss
    #
    @15
    @30
    wceq
    @18
    @0
    @1
    @35
    @2
    @34
    cB
    chlt
    cK
    cM
    cX
    pmapj2.b
    @34
    eqid
    #
    pmapj2.m
    pmapssat
    3adant3
    @0
    @2
    @36
    @1
    @34
    cB
    chlt
    cK
    cM
    cY
    pmapj2.b
    @37
    pmapj2.m
    pmapssat
    3adant2
    @34
    c.pl
    @13
    @14
    cK
    c.pe
    @37
    pmapj2.p
    pmapj2.o
    poldmj1N
    syl3anc
    @3
    @0
    @20
    @21
    @9
    @33
    wceq
    @18
    @25
    @26
    @34
    cB
    cM
    cK
    @7
    @5
    @6
    pmapj2.b
    @27
    @37
    pmapj2.m
    pmapmeet
    syl3anc
    3eqtr4rd
    fveq2d
    @3
    @11
    @16
    cM
    @0
    cK
    col
    wcel
    @1
    @2
    @11
    @16
    wceq
    cK
    hlol
    cB
    c.or
    cK
    @7
    @4
    cX
    cY
    pmapj2.b
    pmapj2.j
    @27
    @24
    oldmm4
    syl3an1
    fveq2d
    3eqtr3rd
end
