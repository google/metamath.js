include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "nonconne.mm"
include "wss.mm"
include "wcel.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "chlt.mm"
include "lssss.mm"
include "syl.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "cv.mm"
include "wrex.mm"
include "adantr.mm"
include "lss1.mm"
include "wpss.mm"
include "df-pss.mm"
include "biimpri.mm"
include "adantl.mm"
include "lpssat.mm"
include "ex.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "eqid.mm"
include "csn.mm"
include "simp3.mm"
include "dochexmidlem6.mm"
include "dochexmidlem7.mm"
include "pm2.21ddne.mm"
include "3adant3l.mm"
include "rexlimdv3a.mm"
include "syld.mm"
include "mpand.mm"
include "necon1bd.mm"
include "mpi.mm"

theorem dochexmidlem8
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vp: setvar p
  assume dochexmidlem1.h: |- H = ( LHyp ` K )
  assume dochexmidlem1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochexmidlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochexmidlem1.v: |- V = ( Base ` U )
  assume dochexmidlem1.s: |- S = ( LSubSp ` U )
  assume dochexmidlem1.n: |- N = ( LSpan ` U )
  assume dochexmidlem1.p: |- .(+) = ( LSSum ` U )
  assume dochexmidlem1.a: |- A = ( LSAtoms ` U )
  assume dochexmidlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochexmidlem1.x: |- ( ph -> X e. S )
  assume dochexmidlem8.z: |- .0. = ( 0g ` U )
  assume dochexmidlem8.xn: |- ( ph -> X =/= { .0. } )
  assume dochexmidlem8.c: |- ( ph -> ( ._|_ ` ( ._|_ ` X ) ) = X )


  assert |- ( ph -> ( X .(+) ( ._|_ ` X ) ) = V )

  proof
    wph
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
    cX
    c.pe
    cfv
    #
    c.po
    co
    #
    cV
    wceq
    cX
    cX
    nonconne
    wph
    @0
    @2
    cV
    wph
    @2
    cV
    wss
    #
    @2
    cV
    wne
    #
    @0
    wph
    @2
    cS
    wcel
    #
    @3
    wph
    cU
    clmod
    wcel
    #
    cX
    cS
    wcel
    #
    @1
    cS
    wcel
    #
    @5
    wph
    cU
    cH
    cK
    cW
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.k
    dvhlmod
    #
    dochexmidlem1.x
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    @8
    dochexmidlem1.k
    wph
    @7
    @11
    dochexmidlem1.x
    cS
    cX
    cV
    cU
    dochexmidlem1.v
    dochexmidlem1.s
    lssss
    syl
    cS
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.s
    dochexmidlem1.o
    dochlss
    syl2anc
    c.po
    cS
    cX
    @1
    cU
    dochexmidlem1.s
    dochexmidlem1.p
    lsmcl
    syl3anc
    #
    cS
    @2
    cV
    cU
    dochexmidlem1.v
    dochexmidlem1.s
    lssss
    syl
    wph
    @3
    @4
    wa
    #
    vp
    cv
    #
    cV
    wss
    #
    @14
    @2
    wss
    wn
    #
    wa
    #
    vp
    cA
    wrex
    #
    @0
    wph
    @13
    @18
    wph
    @13
    wa
    cA
    cS
    @2
    cV
    cU
    vp
    dochexmidlem1.s
    dochexmidlem1.a
    wph
    @6
    @13
    @9
    adantr
    wph
    @5
    @13
    @12
    adantr
    wph
    cV
    cS
    wcel
    #
    @13
    wph
    @6
    @19
    @9
    cS
    cV
    cU
    dochexmidlem1.v
    dochexmidlem1.s
    lss1
    syl
    adantr
    @13
    @2
    cV
    wpss
    #
    wph
    @20
    @13
    @2
    cV
    df-pss
    biimpri
    adantl
    lpssat
    ex
    wph
    @17
    @0
    vp
    cA
    wph
    @14
    cA
    wcel
    #
    @16
    @0
    @15
    wph
    @21
    @16
    w3a
    #
    @0
    cX
    @14
    c.po
    co
    #
    cX
    @22
    cA
    c.po
    cS
    cU
    cH
    cK
    @23
    cN
    c.pe
    cV
    cW
    cX
    c.0
    vp
    dochexmidlem1.h
    dochexmidlem1.o
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.s
    dochexmidlem1.n
    dochexmidlem1.p
    dochexmidlem1.a
    wph
    @21
    @10
    @16
    dochexmidlem1.k
    3ad2ant1
    #
    wph
    @21
    @7
    @16
    dochexmidlem1.x
    3ad2ant1
    #
    wph
    @21
    @16
    simp2
    #
    dochexmidlem8.z
    @23
    eqid
    #
    wph
    @21
    cX
    c.0
    csn
    wne
    @16
    dochexmidlem8.xn
    3ad2ant1
    #
    wph
    @21
    @1
    c.pe
    cfv
    cX
    wceq
    @16
    dochexmidlem8.c
    3ad2ant1
    #
    wph
    @21
    @16
    simp3
    #
    dochexmidlem6
    @22
    cA
    c.po
    cS
    cU
    cH
    cK
    @23
    cN
    c.pe
    cV
    cW
    cX
    c.0
    vp
    dochexmidlem1.h
    dochexmidlem1.o
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.s
    dochexmidlem1.n
    dochexmidlem1.p
    dochexmidlem1.a
    @24
    @25
    @26
    dochexmidlem8.z
    @27
    @28
    @29
    @30
    dochexmidlem7
    pm2.21ddne
    3adant3l
    rexlimdv3a
    syld
    mpand
    necon1bd
    mpi
end
