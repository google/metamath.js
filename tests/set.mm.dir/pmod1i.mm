include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "cjn.mm"
include "cfv.mm"
include "cple.mm"
include "eqid.mm"
include "pmodlem2.mm"
include "3expa.mm"
include "inss1.mm"
include "wi.mm"
include "simpll.mm"
include "simplr2.mm"
include "simplr1.mm"
include "paddss2.mm"
include "syl3anc.mm"
include "mpi.mm"
include "simpl.mm"
include "psubssat.mm"
include "3ad2antr3.mm"
include "simpr2.mm"
include "ssinss1.mm"
include "syl.mm"
include "paddss1.mm"
include "imp.mm"
include "simplr3.mm"
include "syl2anc.mm"
include "inss2.mm"
include "paddidm.mm"
include "sseqtrd.mm"
include "sstrd.mm"
include "ssind.mm"
include "eqssd.mm"
include "ex.mm"

theorem pmod1i
  let cA: class A
  let c.pl: class .+
  let cS: class S
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume pmod.a: |- A = ( Atoms ` K )
  assume pmod.s: |- S = ( PSubSp ` K )
  assume pmod.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ ( X C_ A /\ Y C_ A /\ Z e. S ) ) -> ( X C_ Z -> ( ( X .+ Y ) i^i Z ) = ( X .+ ( Y i^i Z ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    cZ
    cS
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cZ
    wss
    #
    cX
    cY
    c.pl
    co
    #
    cZ
    cin
    #
    cX
    cY
    cZ
    cin
    #
    c.pl
    co
    #
    wceq
    @5
    @6
    wa
    #
    @8
    @10
    @0
    @4
    @6
    @8
    @10
    wss
    cA
    c.pl
    cS
    cK
    cjn
    cfv
    #
    cK
    cK
    cple
    cfv
    #
    cX
    cY
    cZ
    @13
    eqid
    @12
    eqid
    pmod.a
    pmod.s
    pmod.p
    pmodlem2
    3expa
    @11
    @10
    @7
    cZ
    @11
    @9
    cY
    wss
    #
    @10
    @7
    wss
    #
    cY
    cZ
    inss1
    @11
    @0
    @2
    @1
    @14
    @15
    wi
    @0
    @4
    @6
    simpll
    #
    @1
    @2
    @3
    @0
    @6
    simplr2
    @1
    @2
    @3
    @0
    @6
    simplr1
    cA
    chlt
    c.pl
    cK
    @9
    cY
    cX
    pmod.a
    pmod.p
    paddss2
    syl3anc
    mpi
    @11
    @10
    cZ
    @9
    c.pl
    co
    #
    cZ
    @5
    @6
    @10
    @17
    wss
    #
    @5
    @0
    cZ
    cA
    wss
    #
    @9
    cA
    wss
    #
    @6
    @18
    wi
    @0
    @4
    simpl
    @0
    @1
    @3
    @19
    @2
    cA
    chlt
    cS
    cK
    cZ
    pmod.a
    pmod.s
    psubssat
    #
    3ad2antr3
    @5
    @2
    @20
    @0
    @1
    @2
    @3
    simpr2
    cY
    cZ
    cA
    ssinss1
    syl
    cA
    chlt
    c.pl
    cK
    cX
    cZ
    @9
    pmod.a
    pmod.p
    paddss1
    syl3anc
    imp
    @11
    @17
    cZ
    cZ
    c.pl
    co
    #
    cZ
    @11
    @0
    @19
    @19
    @17
    @22
    wss
    #
    @16
    @11
    @0
    @3
    @19
    @16
    @1
    @2
    @3
    @0
    @6
    simplr3
    #
    @21
    syl2anc
    #
    @25
    @0
    @19
    @19
    w3a
    @9
    cZ
    wss
    @23
    cY
    cZ
    inss2
    cA
    chlt
    c.pl
    cK
    @9
    cZ
    cZ
    pmod.a
    pmod.p
    paddss2
    mpi
    syl3anc
    @11
    @0
    @3
    @22
    cZ
    wceq
    @16
    @24
    chlt
    c.pl
    cS
    cK
    cZ
    pmod.s
    pmod.p
    paddidm
    syl2anc
    sseqtrd
    sstrd
    ssind
    eqssd
    ex
end
