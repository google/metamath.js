include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "pmapj2N.mm"
include "fveq2d.mm"
include "wceq.mm"
include "simp1.mm"
include "clat.mm"
include "hllat.mm"
include "latjcl.mm"
include "syl3an1.mm"
include "polpmapN.mm"
include "syl2anc.mm"
include "catm.mm"
include "wss.mm"
include "eqid.mm"
include "pmapssat.mm"
include "3adant3.mm"
include "3adant2.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "3polN.mm"
include "3eqtr3d.mm"

theorem pmapocjN
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cN: class N
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume pmapocj.b: |- B = ( Base ` K )
  assume pmapocj.j: |- .\/ = ( join ` K )
  assume pmapocj.m: |- ./\ = ( meet ` K )
  assume pmapocj.o: |- ._|_ = ( oc ` K )
  assume pmapocj.f: |- F = ( pmap ` K )
  assume pmapocj.p: |- .+ = ( +P ` K )
  assume pmapocj.r: |- N = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( F ` ( ._|_ ` ( X .\/ Y ) ) ) = ( N ` ( ( F ` X ) .+ ( F ` Y ) ) ) )

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
    cY
    c.or
    co
    #
    cF
    cfv
    #
    cN
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    c.pl
    co
    #
    cN
    cfv
    #
    cN
    cfv
    #
    cN
    cfv
    #
    @4
    c.pe
    cfv
    cF
    cfv
    #
    @10
    @3
    @5
    @11
    cN
    cB
    c.pl
    c.or
    cK
    cF
    cN
    cX
    cY
    pmapocj.b
    pmapocj.j
    pmapocj.f
    pmapocj.p
    pmapocj.r
    pmapj2N
    fveq2d
    @3
    @0
    @4
    cB
    wcel
    #
    @6
    @13
    wceq
    @0
    @1
    @2
    simp1
    #
    @0
    cK
    clat
    wcel
    @1
    @2
    @14
    cK
    hllat
    cB
    c.or
    cK
    cX
    cY
    pmapocj.b
    pmapocj.j
    latjcl
    syl3an1
    cB
    cN
    cK
    cF
    c.pe
    @4
    pmapocj.b
    pmapocj.o
    pmapocj.f
    pmapocj.r
    polpmapN
    syl2anc
    @3
    @0
    @9
    cK
    catm
    cfv
    #
    wss
    #
    @12
    @10
    wceq
    @15
    @3
    @0
    @7
    @16
    wss
    #
    @8
    @16
    wss
    #
    @17
    @15
    @0
    @1
    @18
    @2
    @16
    cB
    chlt
    cK
    cF
    cX
    pmapocj.b
    @16
    eqid
    #
    pmapocj.f
    pmapssat
    3adant3
    @0
    @2
    @19
    @1
    @16
    cB
    chlt
    cK
    cF
    cY
    pmapocj.b
    @20
    pmapocj.f
    pmapssat
    3adant2
    @16
    chlt
    c.pl
    cK
    @7
    @8
    @20
    pmapocj.p
    paddssat
    syl3anc
    @16
    @9
    cK
    cN
    @20
    pmapocj.r
    3polN
    syl2anc
    3eqtr3d
end
