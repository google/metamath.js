include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cun.mm"
include "club.mm"
include "coc.mm"
include "cpmap.mm"
include "cin.mm"
include "paddunN.mm"
include "wceq.mm"
include "simp1.mm"
include "wa.mm"
include "unss.mm"
include "biimpi.mm"
include "3adant1.mm"
include "eqid.mm"
include "polval2N.mm"
include "syl2anc.mm"
include "cmee.mm"
include "cbs.mm"
include "cops.mm"
include "hlop.mm"
include "3ad2ant1.mm"
include "ccla.mm"
include "hlclat.mm"
include "simp2.mm"
include "atssbase.mm"
include "syl6ss.mm"
include "clatlubcl.mm"
include "opoccl.mm"
include "simp3.mm"
include "pmapmeet.mm"
include "syl3anc.mm"
include "cjn.mm"
include "lubun.mm"
include "fveq2d.mm"
include "col.mm"
include "hlol.mm"
include "oldmj1.mm"
include "eqtrd.mm"
include "3adant3.mm"
include "3adant2.mm"
include "ineq12d.mm"
include "3eqtr4d.mm"
include "3eqtrd.mm"

theorem poldmj1N
  let cA: class A
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cK: class K
  let c.pe: class ._|_
  assume paddun.a: |- A = ( Atoms ` K )
  assume paddun.p: |- .+ = ( +P ` K )
  assume paddun.o: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ S C_ A /\ T C_ A ) -> ( ._|_ ` ( S .+ T ) ) = ( ( ._|_ ` S ) i^i ( ._|_ ` T ) ) )

  proof
    cK
    chlt
    wcel
    #
    cS
    cA
    wss
    #
    cT
    cA
    wss
    #
    w3a
    #
    cS
    cT
    c.pl
    co
    c.pe
    cfv
    cS
    cT
    cun
    #
    c.pe
    cfv
    #
    @4
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
    c.pe
    cfv
    #
    cT
    c.pe
    cfv
    #
    cin
    #
    cA
    c.pl
    cS
    cT
    cK
    c.pe
    paddun.a
    paddun.p
    paddun.o
    paddunN
    @3
    @0
    @4
    cA
    wss
    #
    @5
    @11
    wceq
    @0
    @1
    @2
    simp1
    #
    @1
    @2
    @15
    @0
    @1
    @2
    wa
    @15
    cS
    cT
    cA
    unss
    biimpi
    3adant1
    cA
    c.pe
    @6
    cK
    @10
    @8
    @4
    @6
    eqid
    #
    @8
    eqid
    #
    paddun.a
    @10
    eqid
    #
    paddun.o
    polval2N
    syl2anc
    @3
    cS
    @6
    cfv
    #
    @8
    cfv
    #
    cT
    @6
    cfv
    #
    @8
    cfv
    #
    cK
    cmee
    cfv
    #
    co
    #
    @10
    cfv
    #
    @21
    @10
    cfv
    #
    @23
    @10
    cfv
    #
    cin
    #
    @11
    @14
    @3
    @0
    @21
    cK
    cbs
    cfv
    #
    wcel
    #
    @23
    @30
    wcel
    #
    @26
    @29
    wceq
    @16
    @3
    cK
    cops
    wcel
    #
    @20
    @30
    wcel
    #
    @31
    @0
    @1
    @33
    @2
    cK
    hlop
    3ad2ant1
    #
    @3
    cK
    ccla
    wcel
    #
    cS
    @30
    wss
    #
    @34
    @0
    @1
    @36
    @2
    cK
    hlclat
    3ad2ant1
    #
    @3
    cS
    cA
    @30
    @0
    @1
    @2
    simp2
    cA
    @30
    cK
    @30
    eqid
    #
    paddun.a
    atssbase
    #
    syl6ss
    #
    @30
    cS
    @6
    cK
    @39
    @17
    clatlubcl
    syl2anc
    #
    @30
    cK
    @8
    @20
    @39
    @18
    opoccl
    syl2anc
    @3
    @33
    @22
    @30
    wcel
    #
    @32
    @35
    @3
    @36
    cT
    @30
    wss
    #
    @43
    @38
    @3
    cT
    cA
    @30
    @0
    @1
    @2
    simp3
    @40
    syl6ss
    #
    @30
    cT
    @6
    cK
    @39
    @17
    clatlubcl
    syl2anc
    #
    @30
    cK
    @8
    @22
    @39
    @18
    opoccl
    syl2anc
    cA
    @30
    @10
    cK
    @24
    @21
    @23
    @39
    @24
    eqid
    #
    paddun.a
    @19
    pmapmeet
    syl3anc
    @3
    @9
    @25
    @10
    @3
    @9
    @20
    @22
    cK
    cjn
    cfv
    #
    co
    #
    @8
    cfv
    #
    @25
    @3
    @7
    @49
    @8
    @3
    @36
    @37
    @44
    @7
    @49
    wceq
    @38
    @41
    @45
    @30
    cS
    cT
    @6
    @48
    cK
    @39
    @48
    eqid
    #
    @17
    lubun
    syl3anc
    fveq2d
    @3
    cK
    col
    wcel
    #
    @34
    @43
    @50
    @25
    wceq
    @0
    @1
    @52
    @2
    cK
    hlol
    3ad2ant1
    @42
    @46
    @30
    @48
    cK
    @24
    @8
    @20
    @22
    @39
    @51
    @47
    @18
    oldmj1
    syl3anc
    eqtrd
    fveq2d
    @3
    @12
    @27
    @13
    @28
    @0
    @1
    @12
    @27
    wceq
    @2
    cA
    c.pe
    @6
    cK
    @10
    @8
    cS
    @17
    @18
    paddun.a
    @19
    paddun.o
    polval2N
    3adant3
    @0
    @2
    @13
    @28
    wceq
    @1
    cA
    c.pe
    @6
    cK
    @10
    @8
    cT
    @17
    @18
    paddun.a
    @19
    paddun.o
    polval2N
    3adant2
    ineq12d
    3eqtr4d
    3eqtrd
end
