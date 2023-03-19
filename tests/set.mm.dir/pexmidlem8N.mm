include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "co.mm"
include "nonconne.mm"
include "simpll.mm"
include "simplr.mm"
include "polssatN.mm"
include "adantr.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "cv.mm"
include "wrex.mm"
include "wex.mm"
include "wpss.mm"
include "df-pss.mm"
include "pssnel.mm"
include "sylbir.mm"
include "df-rex.mm"
include "sylibr.mm"
include "csn.mm"
include "simplll.mm"
include "simpllr.mm"
include "simprl.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprr.mm"
include "w3a.mm"
include "cjn.mm"
include "cple.mm"
include "eqid.mm"
include "pexmidlem6N.mm"
include "pexmidlem7N.mm"
include "jca.mm"
include "syl33anc.mm"
include "2false.mm"
include "sylib.mm"
include "rexlimdvaa.mm"
include "syl5.mm"
include "mpand.mm"
include "necon1bd.mm"
include "mpi.mm"

theorem pexmidlem8N
  let cA: class A
  let c.pl: class .+
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let vp: setvar p
  assume pexmidALT.a: |- A = ( Atoms ` K )
  assume pexmidALT.p: |- .+ = ( +P ` K )
  assume pexmidALT.o: |- ._|_ = ( _|_P ` K )


  assert |- ( ( ( K e. HL /\ X C_ A ) /\ ( ( ._|_ ` ( ._|_ ` X ) ) = X /\ X =/= (/) ) ) -> ( X .+ ( ._|_ ` X ) ) = A )

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
    wceq
    #
    cX
    c0
    wne
    #
    wa
    #
    wa
    #
    cX
    cX
    wceq
    cX
    cX
    wne
    wa
    #
    wn
    cX
    @3
    c.pl
    co
    #
    cA
    wceq
    cX
    cX
    nonconne
    #
    @7
    @8
    @9
    cA
    @7
    @9
    cA
    wss
    #
    @9
    cA
    wne
    #
    @8
    @7
    @0
    @1
    @3
    cA
    wss
    #
    @11
    @0
    @1
    @6
    simpll
    @0
    @1
    @6
    simplr
    @2
    @13
    @6
    cA
    cK
    c.pe
    cX
    pexmidALT.a
    pexmidALT.o
    polssatN
    adantr
    cA
    chlt
    c.pl
    cK
    cX
    @3
    pexmidALT.a
    pexmidALT.p
    paddssat
    syl3anc
    @11
    @12
    wa
    #
    vp
    cv
    #
    @9
    wcel
    wn
    #
    vp
    cA
    wrex
    #
    @7
    @8
    @14
    @15
    cA
    wcel
    #
    @16
    wa
    #
    vp
    wex
    #
    @17
    @14
    @9
    cA
    wpss
    @20
    @9
    cA
    df-pss
    vp
    @9
    cA
    pssnel
    sylbir
    @16
    vp
    cA
    df-rex
    sylibr
    @7
    @16
    @8
    vp
    cA
    @7
    @19
    wa
    #
    cX
    @15
    csn
    c.pl
    co
    #
    cX
    wceq
    #
    @22
    cX
    wne
    #
    wa
    #
    @8
    @21
    @0
    @1
    @18
    @4
    @5
    @16
    @25
    @0
    @1
    @6
    @19
    simplll
    @0
    @1
    @6
    @19
    simpllr
    @7
    @18
    @16
    simprl
    @2
    @4
    @5
    @19
    simplrl
    @2
    @4
    @5
    @19
    simplrr
    @7
    @18
    @16
    simprr
    @0
    @1
    @18
    w3a
    @4
    @5
    @16
    w3a
    wa
    @23
    @24
    cA
    c.pl
    cK
    cjn
    cfv
    #
    cK
    cK
    cple
    cfv
    #
    @22
    c.pe
    cX
    vp
    @27
    eqid
    #
    @26
    eqid
    #
    pexmidALT.a
    pexmidALT.p
    pexmidALT.o
    @22
    eqid
    #
    pexmidlem6N
    cA
    c.pl
    @26
    cK
    @27
    @22
    c.pe
    cX
    vp
    @28
    @29
    pexmidALT.a
    pexmidALT.p
    pexmidALT.o
    @30
    pexmidlem7N
    jca
    syl33anc
    @25
    @8
    @22
    cX
    nonconne
    @10
    2false
    sylib
    rexlimdvaa
    syl5
    mpand
    necon1bd
    mpi
end
