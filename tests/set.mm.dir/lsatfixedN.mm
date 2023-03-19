include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "cdif.mm"
include "wrex.mm"
include "co.mm"
include "wcel.mm"
include "clvec.mm"
include "wb.mm"
include "islsat.mm"
include "syl.mm"
include "mpbid.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "eldifad.mm"
include "simp3.mm"
include "eqcomd.mm"
include "wne.mm"
include "eqnetrd.mm"
include "lspsnne1.mm"
include "cpr.mm"
include "wss.mm"
include "eqsstrd.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "lveclmod.mm"
include "lspprcl.mm"
include "lspsnel5.mm"
include "mpbird.mm"
include "lspfixed.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl2.mm"
include "snssd.mm"
include "lspssv.mm"
include "syl2anc.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "lspsncmp.mm"
include "lspsncl.mm"
include "simpl3.mm"
include "eqeq1d.mm"
include "3bitr4rd.mm"
include "rexbidva.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem lsatfixedN
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let c.pl: class .+
  let cQ: class Q
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vw: setvar w
  assume lsatfixed.v: |- V = ( Base ` W )
  assume lsatfixed.p: |- .+ = ( +g ` W )
  assume lsatfixed.o: |- .0. = ( 0g ` W )
  assume lsatfixed.n: |- N = ( LSpan ` W )
  assume lsatfixed.a: |- A = ( LSAtoms ` W )
  assume lsatfixed.w: |- ( ph -> W e. LVec )
  assume lsatfixed.q: |- ( ph -> Q e. A )
  assume lsatfixed.x: |- ( ph -> X e. V )
  assume lsatfixed.y: |- ( ph -> Y e. V )
  assume lsatfixed.e: |- ( ph -> Q =/= ( N ` { X } ) )
  assume lsatfixed.f: |- ( ph -> Q =/= ( N ` { Y } ) )
  assume lsatfixed.g: |- ( ph -> Q C_ ( N ` { X , Y } ) )

  disjoint N z
  disjoint .0. z
  disjoint .+ z
  disjoint ph z
  disjoint Q z
  disjoint V z
  disjoint W z
  disjoint X z
  disjoint Y z
  disjoint w z
  disjoint N w
  disjoint .0. w
  disjoint .+ w
  disjoint ph w
  disjoint Q w
  disjoint V w
  disjoint W w
  disjoint X w
  disjoint Y w
  assert |- ( ph -> E. z e. ( ( N ` { Y } ) \ { .0. } ) Q = ( N ` { ( X .+ z ) } ) )

  proof
    wph
    cQ
    vw
    cv
    #
    csn
    cN
    cfv
    #
    wceq
    #
    vw
    cV
    c.0
    csn
    #
    cdif
    #
    wrex
    #
    cQ
    cX
    vz
    cv
    #
    c.pl
    co
    #
    csn
    cN
    cfv
    #
    wceq
    #
    vz
    cY
    csn
    #
    cN
    cfv
    #
    @3
    cdif
    #
    wrex
    #
    wph
    cQ
    cA
    wcel
    #
    @5
    lsatfixed.q
    wph
    cW
    clvec
    wcel
    #
    @14
    @5
    wb
    lsatfixed.w
    vw
    cA
    cQ
    cN
    cV
    cW
    clvec
    c.0
    lsatfixed.v
    lsatfixed.n
    lsatfixed.o
    lsatfixed.a
    islsat
    syl
    mpbid
    wph
    @2
    @13
    vw
    @4
    wph
    @0
    @4
    wcel
    #
    @2
    w3a
    #
    @13
    @0
    @8
    wcel
    #
    vz
    @12
    wrex
    @17
    vz
    c.pl
    cN
    cV
    cW
    @0
    cX
    c.0
    cY
    lsatfixed.v
    lsatfixed.p
    lsatfixed.o
    lsatfixed.n
    wph
    @16
    @15
    @2
    lsatfixed.w
    3ad2ant1
    #
    @17
    @0
    cV
    @3
    wph
    @16
    @2
    simp2
    #
    eldifad
    #
    wph
    @16
    cX
    cV
    wcel
    #
    @2
    lsatfixed.x
    3ad2ant1
    #
    wph
    @16
    cY
    cV
    wcel
    @2
    lsatfixed.y
    3ad2ant1
    #
    @17
    cN
    cV
    cW
    @0
    cX
    c.0
    lsatfixed.v
    lsatfixed.o
    lsatfixed.n
    @19
    @20
    @23
    @17
    @1
    cQ
    cX
    csn
    cN
    cfv
    #
    @17
    cQ
    @1
    wph
    @16
    @2
    simp3
    eqcomd
    #
    wph
    @16
    cQ
    @25
    wne
    @2
    lsatfixed.e
    3ad2ant1
    eqnetrd
    lspsnne1
    @17
    cN
    cV
    cW
    @0
    cY
    c.0
    lsatfixed.v
    lsatfixed.o
    lsatfixed.n
    @19
    @20
    @24
    @17
    @1
    cQ
    @11
    @26
    wph
    @16
    cQ
    @11
    wne
    @2
    lsatfixed.f
    3ad2ant1
    eqnetrd
    lspsnne1
    @17
    @0
    cX
    cY
    cpr
    cN
    cfv
    #
    wcel
    @1
    @27
    wss
    @17
    @1
    cQ
    @27
    @26
    wph
    @16
    cQ
    @27
    wss
    @2
    lsatfixed.g
    3ad2ant1
    eqsstrd
    @17
    cW
    clss
    cfv
    #
    @27
    cN
    cV
    cW
    @0
    lsatfixed.v
    @28
    eqid
    #
    lsatfixed.n
    wph
    @16
    cW
    clmod
    wcel
    #
    @2
    wph
    @15
    @30
    lsatfixed.w
    cW
    lveclmod
    syl
    #
    3ad2ant1
    wph
    @16
    @27
    @28
    wcel
    @2
    wph
    @28
    cN
    cV
    cW
    cX
    cY
    lsatfixed.v
    @29
    lsatfixed.n
    @31
    lsatfixed.x
    lsatfixed.y
    lspprcl
    3ad2ant1
    @21
    lspsnel5
    mpbird
    lspfixed
    @17
    @9
    @18
    vz
    @12
    @17
    @6
    @12
    wcel
    #
    wa
    #
    @1
    @8
    wss
    @1
    @8
    wceq
    @18
    @9
    @33
    cN
    cV
    cW
    @0
    @7
    c.0
    lsatfixed.v
    lsatfixed.o
    lsatfixed.n
    @33
    wph
    @15
    wph
    @16
    @2
    @32
    simpl1
    #
    lsatfixed.w
    syl
    wph
    @16
    @2
    @32
    simpl2
    #
    @33
    @30
    @22
    @6
    cV
    wcel
    @7
    cV
    wcel
    #
    @33
    wph
    @30
    @34
    @31
    syl
    #
    @33
    wph
    @22
    @34
    lsatfixed.x
    syl
    @17
    @12
    cV
    @6
    wph
    @16
    @12
    cV
    wss
    @2
    wph
    @11
    cV
    @3
    wph
    @30
    @10
    cV
    wss
    @11
    cV
    wss
    @31
    wph
    cY
    cV
    lsatfixed.y
    snssd
    @10
    cN
    cV
    cW
    lsatfixed.v
    lsatfixed.n
    lspssv
    syl2anc
    ssdifssd
    3ad2ant1
    sselda
    c.pl
    cV
    cW
    cX
    @6
    lsatfixed.v
    lsatfixed.p
    lmodvacl
    syl3anc
    #
    lspsncmp
    @33
    @28
    @8
    cN
    cV
    cW
    @0
    lsatfixed.v
    @29
    lsatfixed.n
    @37
    @33
    @30
    @36
    @8
    @28
    wcel
    @37
    @38
    @28
    cN
    cV
    cW
    @7
    lsatfixed.v
    @29
    lsatfixed.n
    lspsncl
    syl2anc
    @33
    @0
    cV
    @3
    @35
    eldifad
    lspsnel5
    @33
    cQ
    @1
    @8
    wph
    @16
    @2
    @32
    simpl3
    eqeq1d
    3bitr4rd
    rexbidva
    mpbird
    rexlimdv3a
    mpd
end
