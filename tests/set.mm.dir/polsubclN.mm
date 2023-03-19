include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "club.mm"
include "coc.mm"
include "cpmap.mm"
include "eqid.mm"
include "polval2N.mm"
include "cbs.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "ccla.mm"
include "hlclat.mm"
include "atssbase.mm"
include "sstr.mm"
include "mpan2.mm"
include "clatlubcl.mm"
include "syl2an.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "pmapsubclN.mm"
include "syldan.mm"
include "eqeltrd.mm"

theorem polsubclN
  let cA: class A
  let cC: class C
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  assume polsubcl.a: |- A = ( Atoms ` K )
  assume polsubcl.p: |- ._|_ = ( _|_P ` K )
  assume polsubcl.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. HL /\ X C_ A ) -> ( ._|_ ` X ) e. C )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    wa
    #
    cX
    c.pe
    cfv
    cX
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
    cK
    cpmap
    cfv
    #
    cfv
    #
    cC
    cA
    c.pe
    @3
    cK
    @7
    @5
    cX
    @3
    eqid
    #
    @5
    eqid
    #
    polsubcl.a
    @7
    eqid
    #
    polsubcl.p
    polval2N
    @0
    @1
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @8
    cC
    wcel
    @2
    cK
    cops
    wcel
    #
    @4
    @12
    wcel
    #
    @13
    @0
    @14
    @1
    cK
    hlop
    adantr
    @0
    cK
    ccla
    wcel
    cX
    @12
    wss
    #
    @15
    @1
    cK
    hlclat
    @1
    cA
    @12
    wss
    @16
    cA
    @12
    cK
    @12
    eqid
    #
    polsubcl.a
    atssbase
    cX
    cA
    @12
    sstr
    mpan2
    @12
    cX
    @3
    cK
    @17
    @9
    clatlubcl
    syl2an
    @12
    cK
    @5
    @4
    @17
    @10
    opoccl
    syl2anc
    @12
    cC
    cK
    @7
    @6
    @17
    @11
    polsubcl.c
    pmapsubclN
    syldan
    eqeltrd
end
