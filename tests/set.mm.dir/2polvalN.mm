include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "coc.mm"
include "eqid.mm"
include "polval2N.mm"
include "fveq2d.mm"
include "cbs.mm"
include "wceq.mm"
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
include "polpmapN.mm"
include "syldan.mm"
include "opococ.mm"
include "3eqtrd.mm"

theorem 2polvalN
  let cA: class A
  let cU: class U
  let cK: class K
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  assume 2polval.u: |- U = ( lub ` K )
  assume 2polval.a: |- A = ( Atoms ` K )
  assume 2polval.m: |- M = ( pmap ` K )
  assume 2polval.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X C_ A ) -> ( ._|_ ` ( ._|_ ` X ) ) = ( M ` ( U ` X ) ) )

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
    #
    c.pe
    cfv
    cX
    cU
    cfv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    cM
    cfv
    #
    c.pe
    cfv
    #
    @6
    @5
    cfv
    #
    cM
    cfv
    #
    @4
    cM
    cfv
    @2
    @3
    @7
    c.pe
    cA
    c.pe
    cU
    cK
    cM
    @5
    cX
    2polval.u
    @5
    eqid
    #
    2polval.a
    2polval.m
    2polval.p
    polval2N
    fveq2d
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
    @10
    wceq
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
    #
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
    @17
    cA
    @12
    cK
    @12
    eqid
    #
    2polval.a
    atssbase
    cX
    cA
    @12
    sstr
    mpan2
    @12
    cX
    cU
    cK
    @18
    2polval.u
    clatlubcl
    syl2an
    #
    @12
    cK
    @5
    @4
    @18
    @11
    opoccl
    syl2anc
    @12
    c.pe
    cK
    cM
    @5
    @6
    @18
    @11
    2polval.m
    2polval.p
    polpmapN
    syldan
    @2
    @9
    @4
    cM
    @2
    @14
    @15
    @9
    @4
    wceq
    @16
    @19
    @12
    cK
    @5
    @4
    @18
    @11
    opococ
    syl2anc
    fveq2d
    3eqtrd
end
