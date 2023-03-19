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
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "adantr.mm"
include "cops.mm"
include "hlop.mm"
include "ccla.mm"
include "hlclat.mm"
include "atssbase.mm"
include "sstr.mm"
include "mpan2.mm"
include "clatlubcl.mm"
include "syl2an.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "pmapsub.mm"
include "eqeltrd.mm"

theorem polsubN
  let cA: class A
  let cS: class S
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  assume polsubsp.a: |- A = ( Atoms ` K )
  assume polsubsp.s: |- S = ( PSubSp ` K )
  assume polsubsp.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X C_ A ) -> ( ._|_ ` X ) e. S )

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
    cS
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
    polsubsp.a
    @7
    eqid
    #
    polsubsp.p
    polval2N
    @2
    cK
    clat
    wcel
    #
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @8
    cS
    wcel
    @0
    @12
    @1
    cK
    hllat
    adantr
    @2
    cK
    cops
    wcel
    #
    @4
    @13
    wcel
    #
    @14
    @0
    @15
    @1
    cK
    hlop
    adantr
    @0
    cK
    ccla
    wcel
    cX
    @13
    wss
    #
    @16
    @1
    cK
    hlclat
    @1
    cA
    @13
    wss
    @17
    cA
    @13
    cK
    @13
    eqid
    #
    polsubsp.a
    atssbase
    cX
    cA
    @13
    sstr
    mpan2
    @13
    cX
    @3
    cK
    @18
    @9
    clatlubcl
    syl2an
    @13
    cK
    @5
    @4
    @18
    @10
    opoccl
    syl2anc
    @13
    cS
    cK
    @7
    @6
    @18
    polsubsp.s
    @11
    pmapsub
    syl2anc
    eqeltrd
end
