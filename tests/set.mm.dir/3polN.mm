include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "club.mm"
include "cfv.mm"
include "cpmap.mm"
include "coc.mm"
include "cbs.mm"
include "wceq.mm"
include "ccla.mm"
include "hlclat.mm"
include "eqid.mm"
include "atssbase.mm"
include "sstr.mm"
include "mpan2.mm"
include "clatlubcl.mm"
include "syl2an.mm"
include "polpmapN.mm"
include "syldan.mm"
include "2polvalN.mm"
include "fveq2d.mm"
include "polval2N.mm"
include "3eqtr4d.mm"

theorem 3polN
  let cA: class A
  let cS: class S
  let cK: class K
  let c.pe: class ._|_
  let vp: setvar p
  let cX: class X
  let cY: class Y
  assume 2polss.a: |- A = ( Atoms ` K )
  assume 2polss.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ S C_ A ) -> ( ._|_ ` ( ._|_ ` ( ._|_ ` S ) ) ) = ( ._|_ ` S ) )

  proof
    cK
    chlt
    wcel
    #
    cS
    cA
    wss
    #
    wa
    #
    cS
    cK
    club
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
    c.pe
    cfv
    #
    @4
    cK
    coc
    cfv
    #
    cfv
    @5
    cfv
    #
    cS
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    @10
    @0
    @1
    @4
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @9
    wceq
    @0
    cK
    ccla
    wcel
    cS
    @12
    wss
    #
    @13
    @1
    cK
    hlclat
    @1
    cA
    @12
    wss
    @14
    cA
    @12
    cK
    @12
    eqid
    #
    2polss.a
    atssbase
    cS
    cA
    @12
    sstr
    mpan2
    @12
    cS
    @3
    cK
    @15
    @3
    eqid
    #
    clatlubcl
    syl2an
    @12
    c.pe
    cK
    @5
    @8
    @4
    @15
    @8
    eqid
    #
    @5
    eqid
    #
    2polss.p
    polpmapN
    syldan
    @2
    @11
    @6
    c.pe
    cA
    @3
    cK
    @5
    c.pe
    cS
    @16
    2polss.a
    @18
    2polss.p
    2polvalN
    fveq2d
    cA
    c.pe
    @3
    cK
    @5
    @8
    cS
    @16
    @17
    2polss.a
    @18
    2polss.p
    polval2N
    3eqtr4d
end
