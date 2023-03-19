include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wn.mm"
include "cin.mm"
include "inass.mm"
include "wceq.mm"
include "simp11.mm"
include "simp13.mm"
include "simp21.mm"
include "osumcllem3N.mm"
include "syl3anc.mm"
include "ineq1d.mm"
include "syl5eqr.mm"
include "simp12.mm"
include "psubclssatN.mm"
include "syl2anc.mm"
include "simp22.mm"
include "paddssat.mm"
include "polssatN.mm"
include "syl5eqss.mm"
include "simp23.mm"
include "sseldd.mm"
include "simp3.mm"
include "osumcllem8N.mm"
include "syl331anc.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "pol0N.mm"
include "syl.mm"
include "osumcllem1N.mm"
include "syl31anc.mm"
include "ineq12d.mm"
include "polsubclN.mm"
include "syl5eqel.mm"
include "csn.mm"
include "paddatclN.mm"
include "psubclinN.mm"
include "osumcllem2N.mm"
include "poml6N.mm"
include "snssd.mm"
include "sseqin2.mm"
include "sylib.mm"
include "3eqtr3rd.mm"

theorem osumcllem9N
  let cA: class A
  let cC: class C
  let c.pl: class .+
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume osumcllem.l: |- .<_ = ( le ` K )
  assume osumcllem.j: |- .\/ = ( join ` K )
  assume osumcllem.a: |- A = ( Atoms ` K )
  assume osumcllem.p: |- .+ = ( +P ` K )
  assume osumcllem.o: |- ._|_ = ( _|_P ` K )
  assume osumcllem.c: |- C = ( PSubCl ` K )
  assume osumcllem.m: |- M = ( X .+ { p } )
  assume osumcllem.u: |- U = ( ._|_ ` ( ._|_ ` ( X .+ Y ) ) )


  assert |- ( ( ( K e. HL /\ X e. C /\ Y e. C ) /\ ( X C_ ( ._|_ ` Y ) /\ X =/= (/) /\ p e. U ) /\ -. p e. ( X .+ Y ) ) -> M = X )

  proof
    cK
    chlt
    wcel
    #
    cX
    cC
    wcel
    #
    cY
    cC
    wcel
    #
    w3a
    #
    cX
    cY
    c.pe
    cfv
    wss
    #
    cX
    c0
    wne
    #
    vp
    cv
    #
    cU
    wcel
    #
    w3a
    #
    @6
    cX
    cY
    c.pl
    co
    #
    wcel
    wn
    #
    w3a
    #
    cX
    c.pe
    cfv
    #
    cU
    cM
    cin
    #
    cin
    #
    c.pe
    cfv
    #
    @13
    cin
    #
    cA
    cM
    cin
    #
    cX
    cM
    @11
    @15
    cA
    @13
    cM
    @11
    @15
    c0
    c.pe
    cfv
    #
    cA
    @11
    @14
    c0
    c.pe
    @11
    @14
    cY
    cM
    cin
    #
    c0
    @11
    @14
    @12
    cU
    cin
    #
    cM
    cin
    @19
    @12
    cU
    cM
    inass
    @11
    @20
    cY
    cM
    @11
    @0
    @2
    @4
    @20
    cY
    wceq
    @0
    @1
    @2
    @8
    @10
    simp11
    #
    @0
    @1
    @2
    @8
    @10
    simp13
    #
    @3
    @4
    @5
    @7
    @10
    simp21
    #
    cA
    cC
    c.pl
    cU
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    cY
    vp
    osumcllem.l
    osumcllem.j
    osumcllem.a
    osumcllem.p
    osumcllem.o
    osumcllem.c
    osumcllem.m
    osumcllem.u
    osumcllem3N
    syl3anc
    ineq1d
    syl5eqr
    @11
    @0
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    @4
    @5
    @6
    cA
    wcel
    #
    @10
    @19
    c0
    wceq
    @21
    @11
    @0
    @1
    @24
    @21
    @0
    @1
    @2
    @8
    @10
    simp12
    #
    cA
    cC
    chlt
    cK
    cX
    osumcllem.a
    osumcllem.c
    psubclssatN
    syl2anc
    #
    @11
    @0
    @2
    @25
    @21
    @22
    cA
    cC
    chlt
    cK
    cY
    osumcllem.a
    osumcllem.c
    psubclssatN
    syl2anc
    #
    @23
    @3
    @4
    @5
    @7
    @10
    simp22
    @11
    cU
    cA
    @6
    @11
    cU
    @9
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cA
    osumcllem.u
    @11
    @0
    @30
    cA
    wss
    #
    @31
    cA
    wss
    @21
    @11
    @0
    @9
    cA
    wss
    #
    @32
    @21
    @11
    @0
    @24
    @25
    @33
    @21
    @28
    @29
    cA
    chlt
    c.pl
    cK
    cX
    cY
    osumcllem.a
    osumcllem.p
    paddssat
    syl3anc
    cA
    cK
    c.pe
    @9
    osumcllem.a
    osumcllem.o
    polssatN
    syl2anc
    #
    cA
    cK
    c.pe
    @30
    osumcllem.a
    osumcllem.o
    polssatN
    syl2anc
    syl5eqss
    @3
    @4
    @5
    @7
    @10
    simp23
    #
    sseldd
    #
    @3
    @8
    @10
    simp3
    cA
    cC
    c.pl
    cU
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    cY
    vp
    osumcllem.l
    osumcllem.j
    osumcllem.a
    osumcllem.p
    osumcllem.o
    osumcllem.c
    osumcllem.m
    osumcllem.u
    osumcllem8N
    syl331anc
    eqtrd
    fveq2d
    @11
    @0
    @18
    cA
    wceq
    @21
    cA
    chlt
    cK
    c.pe
    osumcllem.a
    osumcllem.o
    pol0N
    syl
    eqtrd
    @11
    @0
    @24
    @25
    @7
    @13
    cM
    wceq
    @21
    @28
    @29
    @35
    cA
    cC
    c.pl
    cU
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    cY
    vp
    osumcllem.l
    osumcllem.j
    osumcllem.a
    osumcllem.p
    osumcllem.o
    osumcllem.c
    osumcllem.m
    osumcllem.u
    osumcllem1N
    syl31anc
    ineq12d
    @11
    @0
    @1
    @13
    cC
    wcel
    #
    cX
    @13
    wss
    #
    @16
    cX
    wceq
    @21
    @27
    @11
    @0
    cU
    cC
    wcel
    cM
    cC
    wcel
    @37
    @21
    @11
    cU
    @31
    cC
    osumcllem.u
    @11
    @0
    @32
    @31
    cC
    wcel
    @21
    @34
    cA
    cC
    cK
    c.pe
    @30
    osumcllem.a
    osumcllem.o
    osumcllem.c
    polsubclN
    syl2anc
    syl5eqel
    @11
    cM
    cX
    @6
    csn
    #
    c.pl
    co
    #
    cC
    osumcllem.m
    @11
    @0
    @1
    @26
    @40
    cC
    wcel
    @21
    @27
    @36
    cA
    cC
    c.pl
    @6
    cK
    cX
    osumcllem.a
    osumcllem.p
    osumcllem.c
    paddatclN
    syl3anc
    syl5eqel
    cC
    cK
    cU
    cM
    osumcllem.c
    psubclinN
    syl3anc
    @11
    @0
    @24
    @25
    @7
    @38
    @21
    @28
    @29
    @35
    cA
    cC
    c.pl
    cU
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    cY
    vp
    osumcllem.l
    osumcllem.j
    osumcllem.a
    osumcllem.p
    osumcllem.o
    osumcllem.c
    osumcllem.m
    osumcllem.u
    osumcllem2N
    syl31anc
    cC
    cK
    c.pe
    cX
    @13
    osumcllem.c
    osumcllem.o
    poml6N
    syl31anc
    @11
    cM
    cA
    wss
    @17
    cM
    wceq
    @11
    cM
    @40
    cA
    osumcllem.m
    @11
    @0
    @24
    @39
    cA
    wss
    @40
    cA
    wss
    @21
    @28
    @11
    @6
    cA
    @36
    snssd
    cA
    chlt
    c.pl
    cK
    cX
    @39
    osumcllem.a
    osumcllem.p
    paddssat
    syl3anc
    syl5eqss
    cM
    cA
    sseqin2
    sylib
    3eqtr3rd
end
