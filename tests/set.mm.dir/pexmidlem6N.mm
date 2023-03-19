include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "co.mm"
include "wn.mm"
include "wa.mm"
include "cin.mm"
include "pexmidlem5N.mm"
include "3adantr1.mm"
include "fveq2d.mm"
include "simpl1.mm"
include "pol0N.mm"
include "syl.mm"
include "eqtrd.mm"
include "ineq1d.mm"
include "simpl2.mm"
include "csn.mm"
include "simpl3.mm"
include "snssd.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "syl5eqss.mm"
include "3jca.mm"
include "sspadd1.mm"
include "syl6sseqr.mm"
include "cpscN.mm"
include "simpr1.mm"
include "wb.mm"
include "eqid.mm"
include "ispsubclN.mm"
include "mpbir2and.mm"
include "paddatclN.mm"
include "syl5eqel.mm"
include "psubcli2N.mm"
include "syl2anc.mm"
include "jca.mm"
include "poml4N.mm"
include "sylc.mm"
include "sseqin2.mm"
include "sylib.mm"
include "3eqtr3rd.mm"

theorem pexmidlem6N
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume pexmidlem.l: |- .<_ = ( le ` K )
  assume pexmidlem.j: |- .\/ = ( join ` K )
  assume pexmidlem.a: |- A = ( Atoms ` K )
  assume pexmidlem.p: |- .+ = ( +P ` K )
  assume pexmidlem.o: |- ._|_ = ( _|_P ` K )
  assume pexmidlem.m: |- M = ( X .+ { p } )


  assert |- ( ( ( K e. HL /\ X C_ A /\ p e. A ) /\ ( ( ._|_ ` ( ._|_ ` X ) ) = X /\ X =/= (/) /\ -. p e. ( X .+ ( ._|_ ` X ) ) ) ) -> M = X )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    vp
    cv
    #
    cA
    wcel
    #
    w3a
    #
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cX
    wceq
    #
    cX
    c0
    wne
    #
    @2
    cX
    @5
    c.pl
    co
    wcel
    wn
    #
    w3a
    #
    wa
    #
    cM
    @6
    cX
    @11
    @5
    cM
    cin
    #
    c.pe
    cfv
    #
    cM
    cin
    #
    cA
    cM
    cin
    #
    @6
    cM
    @11
    @13
    cA
    cM
    @11
    @13
    c0
    c.pe
    cfv
    #
    cA
    @11
    @12
    c0
    c.pe
    @4
    @8
    @9
    @12
    c0
    wceq
    @7
    cA
    c.pl
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    vp
    pexmidlem.l
    pexmidlem.j
    pexmidlem.a
    pexmidlem.p
    pexmidlem.o
    pexmidlem.m
    pexmidlem5N
    3adantr1
    fveq2d
    @11
    @0
    @16
    cA
    wceq
    @0
    @1
    @3
    @10
    simpl1
    #
    cA
    chlt
    cK
    c.pe
    pexmidlem.a
    pexmidlem.o
    pol0N
    syl
    eqtrd
    ineq1d
    @11
    @0
    @1
    cM
    cA
    wss
    #
    w3a
    cX
    cM
    wss
    #
    cM
    c.pe
    cfv
    c.pe
    cfv
    cM
    wceq
    #
    wa
    @14
    @6
    wceq
    @11
    @0
    @1
    @18
    @17
    @0
    @1
    @3
    @10
    simpl2
    #
    @11
    cM
    cX
    @2
    csn
    #
    c.pl
    co
    #
    cA
    pexmidlem.m
    @11
    @0
    @1
    @22
    cA
    wss
    #
    @23
    cA
    wss
    @17
    @21
    @11
    @2
    cA
    @0
    @1
    @3
    @10
    simpl3
    #
    snssd
    #
    cA
    chlt
    c.pl
    cK
    cX
    @22
    pexmidlem.a
    pexmidlem.p
    paddssat
    syl3anc
    syl5eqss
    #
    3jca
    @11
    @19
    @20
    @11
    cX
    @23
    cM
    @11
    @0
    @1
    @24
    cX
    @23
    wss
    @17
    @21
    @26
    cA
    chlt
    c.pl
    cK
    cX
    @22
    pexmidlem.a
    pexmidlem.p
    sspadd1
    syl3anc
    pexmidlem.m
    syl6sseqr
    @11
    @0
    cM
    cK
    cpscN
    cfv
    #
    wcel
    @20
    @17
    @11
    cM
    @23
    @28
    pexmidlem.m
    @11
    @0
    cX
    @28
    wcel
    #
    @3
    @23
    @28
    wcel
    @17
    @11
    @29
    @1
    @7
    @21
    @4
    @7
    @8
    @9
    simpr1
    #
    @11
    @0
    @29
    @1
    @7
    wa
    wb
    @17
    cA
    @28
    chlt
    cK
    c.pe
    cX
    pexmidlem.a
    pexmidlem.o
    @28
    eqid
    #
    ispsubclN
    syl
    mpbir2and
    @25
    cA
    @28
    c.pl
    @2
    cK
    cX
    pexmidlem.a
    pexmidlem.p
    @31
    paddatclN
    syl3anc
    syl5eqel
    @28
    chlt
    cK
    c.pe
    cM
    pexmidlem.o
    @31
    psubcli2N
    syl2anc
    jca
    cA
    cK
    c.pe
    cX
    cM
    pexmidlem.a
    pexmidlem.o
    poml4N
    sylc
    @11
    @18
    @15
    cM
    wceq
    @27
    cM
    cA
    sseqin2
    sylib
    3eqtr3rd
    @30
    eqtrd
end
