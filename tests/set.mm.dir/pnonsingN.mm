include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "2polssN.mm"
include "ssrin.mm"
include "syl.mm"
include "club.mm"
include "cpmap.mm"
include "coc.mm"
include "eqid.mm"
include "2polvalN.mm"
include "polval2N.mm"
include "ineq12d.mm"
include "cmee.mm"
include "co.mm"
include "cp0.mm"
include "cops.mm"
include "cbs.mm"
include "hlop.mm"
include "adantr.mm"
include "ccla.mm"
include "hlclat.mm"
include "atssbase.mm"
include "sstr.mm"
include "mpan2.mm"
include "clatlubcl.mm"
include "syl2an.mm"
include "opnoncon.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "simpl.mm"
include "opoccl.mm"
include "pmapmeet.mm"
include "syl3anc.mm"
include "cal.mm"
include "hlatl.mm"
include "pmap0.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "sseqtrd.mm"
include "ss0b.mm"
include "sylib.mm"

theorem pnonsingN
  let cA: class A
  let cP: class P
  let cK: class K
  let cX: class X
  assume 2polat.a: |- A = ( Atoms ` K )
  assume 2polat.p: |- P = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X C_ A ) -> ( X i^i ( P ` X ) ) = (/) )

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
    cX
    cP
    cfv
    #
    cin
    #
    c0
    wss
    @4
    c0
    wceq
    @2
    @4
    @3
    cP
    cfv
    #
    @3
    cin
    #
    c0
    @2
    cX
    @5
    wss
    @4
    @6
    wss
    cA
    cK
    cP
    cX
    2polat.a
    2polat.p
    2polssN
    cX
    @5
    @3
    ssrin
    syl
    @2
    @6
    cX
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
    @8
    cK
    coc
    cfv
    #
    cfv
    #
    @9
    cfv
    #
    cin
    #
    c0
    @2
    @5
    @10
    @3
    @13
    cA
    @7
    cK
    @9
    cP
    cX
    @7
    eqid
    #
    2polat.a
    @9
    eqid
    #
    2polat.p
    2polvalN
    cA
    cP
    @7
    cK
    @9
    @11
    cX
    @15
    @11
    eqid
    #
    2polat.a
    @16
    2polat.p
    polval2N
    ineq12d
    @2
    @8
    @12
    cK
    cmee
    cfv
    #
    co
    #
    @9
    cfv
    #
    cK
    cp0
    cfv
    #
    @9
    cfv
    #
    @14
    c0
    @2
    @19
    @21
    @9
    @2
    cK
    cops
    wcel
    #
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    @19
    @21
    wceq
    @0
    @23
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
    @24
    wss
    #
    @25
    @1
    cK
    hlclat
    @1
    cA
    @24
    wss
    @27
    cA
    @24
    cK
    @24
    eqid
    #
    2polat.a
    atssbase
    cX
    cA
    @24
    sstr
    mpan2
    @24
    cX
    @7
    cK
    @28
    @15
    clatlubcl
    syl2an
    #
    @24
    cK
    @18
    @11
    @8
    @21
    @28
    @17
    @18
    eqid
    #
    @21
    eqid
    #
    opnoncon
    syl2anc
    fveq2d
    @2
    @0
    @25
    @12
    @24
    wcel
    #
    @20
    @14
    wceq
    @0
    @1
    simpl
    @29
    @2
    @23
    @25
    @32
    @26
    @29
    @24
    cK
    @11
    @8
    @28
    @17
    opoccl
    syl2anc
    cA
    @24
    @9
    cK
    @18
    @8
    @12
    @28
    @30
    2polat.a
    @16
    pmapmeet
    syl3anc
    @2
    cK
    cal
    wcel
    #
    @22
    c0
    wceq
    @0
    @33
    @1
    cK
    hlatl
    adantr
    cK
    @9
    @21
    @31
    @16
    pmap0
    syl
    3eqtr3d
    eqtrd
    sseqtrd
    @4
    ss0b
    sylib
end
