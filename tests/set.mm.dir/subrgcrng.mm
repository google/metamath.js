include "ccrg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "crg.mm"
include "cmgp.mm"
include "ccmn.mm"
include "subrgring.mm"
include "adantl.mm"
include "cress.mm"
include "co.mm"
include "eqid.mm"
include "mgpress.mm"
include "cmnd.mm"
include "crngmgp.mm"
include "adantr.mm"
include "ringmgp.mm"
include "syl.mm"
include "eqeltrd.mm"
include "subcmn.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "iscrng.mm"
include "sylanbrc.mm"

theorem subrgcrng
  let cA: class A
  let cR: class R
  let cS: class S
  assume subrgring.1: |- S = ( R |`s A )


  assert |- ( ( R e. CRing /\ A e. ( SubRing ` R ) ) -> S e. CRing )

  proof
    cR
    ccrg
    wcel
    #
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    wa
    #
    cS
    crg
    wcel
    #
    cS
    cmgp
    cfv
    #
    ccmn
    wcel
    cS
    ccrg
    wcel
    @2
    @4
    @0
    cA
    cR
    cS
    subrgring.1
    subrgring
    adantl
    #
    @3
    cR
    cmgp
    cfv
    #
    cA
    cress
    co
    #
    @5
    ccmn
    cA
    cR
    cS
    @7
    ccrg
    @1
    subrgring.1
    @7
    eqid
    #
    mgpress
    #
    @3
    @7
    ccmn
    wcel
    #
    @8
    cmnd
    wcel
    @8
    ccmn
    wcel
    @0
    @11
    @2
    cR
    @7
    @9
    crngmgp
    adantr
    @3
    @8
    @5
    cmnd
    @10
    @3
    @4
    @5
    cmnd
    wcel
    @6
    cS
    @5
    @5
    eqid
    #
    ringmgp
    syl
    eqeltrd
    cA
    @7
    @8
    @8
    eqid
    subcmn
    syl2anc
    eqeltrrd
    cS
    @5
    @12
    iscrng
    sylanbrc
end
