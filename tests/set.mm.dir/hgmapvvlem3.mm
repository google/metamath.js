include "cv.mm"
include "c0g.mm"
include "cfv.mm"
include "wne.mm"
include "csn.mm"
include "wrex.mm"
include "wceq.mm"
include "eqid.mm"
include "cbs.mm"
include "cltrn.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "dochsnnz.mm"
include "clss.mm"
include "wcel.mm"
include "wb.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "snssd.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lssne0.mm"
include "syl.mm"
include "mpbid.mm"
include "w3a.mm"
include "cvsca.mm"
include "co.mm"
include "3ad2ant1.mm"
include "cdif.mm"
include "dochssv.mm"
include "sselda.mm"
include "3adant3.mm"
include "simp3.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "hdmapip1.mm"
include "simpl1.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "cdr.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "adantr.mm"
include "hdmapipcl.mm"
include "hdmapip0.mm"
include "necon3bid.mm"
include "biimp3ar.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
include "simpl2.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "simpr.mm"
include "hgmapvvlem2.mm"
include "mpdan.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hgmapvvlem3
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let c.1: class .1.
  let cE: class E
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vk: setvar k
  assume hdmapglem6.h: |- H = ( LHyp ` K )
  assume hdmapglem6.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapglem6.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmapglem6.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapglem6.v: |- V = ( Base ` U )
  assume hdmapglem6.q: |- .x. = ( .s ` U )
  assume hdmapglem6.r: |- R = ( Scalar ` U )
  assume hdmapglem6.b: |- B = ( Base ` R )
  assume hdmapglem6.t: |- .X. = ( .r ` R )
  assume hdmapglem6.z: |- .0. = ( 0g ` R )
  assume hdmapglem6.i: |- .1. = ( 1r ` R )
  assume hdmapglem6.n: |- N = ( invr ` R )
  assume hdmapglem6.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapglem6.g: |- G = ( ( HGMap ` K ) ` W )
  assume hdmapglem6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapglem6.x: |- ( ph -> X e. ( B \ { .0. } ) )


  assert |- ( ph -> ( G ` ( G ` X ) ) = X )

  proof
    wph
    vk
    cv
    #
    cU
    c0g
    cfv
    #
    wne
    #
    vk
    cE
    csn
    #
    cO
    cfv
    #
    wrex
    #
    cX
    cG
    cfv
    cG
    cfv
    cX
    wceq
    #
    wph
    @4
    @1
    csn
    #
    wne
    #
    @5
    wph
    cU
    cH
    cK
    cO
    cV
    cW
    cE
    @1
    hdmapglem6.h
    hdmapglem6.o
    hdmapglem6.u
    hdmapglem6.v
    @1
    eqid
    #
    hdmapglem6.k
    wph
    cE
    cV
    @7
    wph
    cK
    cbs
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    cE
    cH
    cK
    cV
    cW
    @1
    hdmapglem6.h
    @10
    eqid
    @11
    eqid
    hdmapglem6.u
    hdmapglem6.v
    @9
    hdmapglem6.e
    hdmapglem6.k
    dvheveccl
    eldifad
    #
    dochsnnz
    wph
    @4
    cU
    clss
    cfv
    #
    wcel
    #
    @8
    @5
    wb
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @3
    cV
    wss
    #
    @14
    hdmapglem6.k
    wph
    cE
    cV
    @12
    snssd
    #
    @13
    cU
    cH
    cK
    cO
    cV
    cW
    @3
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.v
    @13
    eqid
    #
    hdmapglem6.o
    dochlss
    syl2anc
    #
    vk
    @13
    cU
    @4
    @1
    @9
    @18
    lssne0
    syl
    mpbid
    wph
    @2
    @6
    vk
    @4
    wph
    @0
    @4
    wcel
    #
    @2
    w3a
    #
    @0
    @0
    cS
    cfv
    #
    cfv
    #
    cN
    cfv
    #
    @0
    cU
    cvsca
    cfv
    #
    co
    #
    @22
    cfv
    c.1
    wceq
    #
    @6
    @21
    cR
    cS
    @25
    cU
    c.1
    cH
    cK
    cN
    cV
    cW
    @0
    @26
    @1
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.v
    @25
    eqid
    #
    @9
    hdmapglem6.r
    hdmapglem6.i
    hdmapglem6.n
    hdmapglem6.s
    wph
    @20
    @15
    @2
    hdmapglem6.k
    3ad2ant1
    @21
    @0
    cV
    wcel
    #
    @2
    @0
    cV
    @7
    cdif
    wcel
    wph
    @20
    @29
    @2
    wph
    @4
    cV
    @0
    wph
    @15
    @16
    @4
    cV
    wss
    hdmapglem6.k
    @17
    cU
    cH
    cK
    cO
    cV
    cW
    @3
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.v
    hdmapglem6.o
    dochssv
    syl2anc
    sselda
    #
    3adant3
    #
    wph
    @20
    @2
    simp3
    @0
    cV
    @1
    eldifsn
    sylanbrc
    @26
    eqid
    hdmapip1
    @21
    @27
    wa
    #
    cB
    @26
    @0
    cR
    cS
    c.x
    c.xp
    cU
    c.1
    cE
    cG
    cH
    cK
    cN
    cO
    cV
    cW
    cX
    c.0
    hdmapglem6.h
    hdmapglem6.e
    hdmapglem6.o
    hdmapglem6.u
    hdmapglem6.v
    hdmapglem6.q
    hdmapglem6.r
    hdmapglem6.b
    hdmapglem6.t
    hdmapglem6.z
    hdmapglem6.i
    hdmapglem6.n
    hdmapglem6.s
    hdmapglem6.g
    @32
    wph
    @15
    wph
    @20
    @2
    @27
    simpl1
    #
    hdmapglem6.k
    syl
    #
    @32
    wph
    cX
    cB
    c.0
    csn
    cdif
    wcel
    @33
    hdmapglem6.x
    syl
    @32
    cU
    clmod
    wcel
    #
    @14
    @24
    cB
    wcel
    #
    @20
    @26
    @4
    wcel
    @32
    wph
    @35
    @33
    wph
    cU
    cH
    cK
    cW
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.k
    dvhlmod
    syl
    @32
    wph
    @14
    @33
    @19
    syl
    @32
    cR
    cdr
    wcel
    #
    @23
    cB
    wcel
    @23
    c.0
    wne
    #
    @36
    @32
    wph
    @37
    @33
    wph
    cU
    clvec
    wcel
    @37
    wph
    cU
    cH
    cK
    cW
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.k
    dvhlvec
    cR
    cU
    hdmapglem6.r
    lvecdrng
    syl
    syl
    @32
    cB
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    @0
    @0
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.v
    hdmapglem6.r
    hdmapglem6.b
    hdmapglem6.s
    @34
    @21
    @29
    @27
    @31
    adantr
    #
    @39
    hdmapipcl
    @21
    @38
    @27
    wph
    @20
    @38
    @2
    wph
    @20
    wa
    #
    @23
    c.0
    @0
    @1
    @40
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    @0
    @1
    c.0
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.v
    @9
    hdmapglem6.r
    hdmapglem6.z
    hdmapglem6.s
    wph
    @15
    @20
    hdmapglem6.k
    adantr
    @30
    hdmapip0
    necon3bid
    biimp3ar
    adantr
    cB
    cR
    cN
    @23
    c.0
    hdmapglem6.b
    hdmapglem6.z
    hdmapglem6.n
    drnginvrcl
    syl3anc
    wph
    @20
    @2
    @27
    simpl2
    #
    cB
    @13
    @25
    @4
    cR
    cU
    @24
    @0
    hdmapglem6.r
    @28
    hdmapglem6.b
    @18
    lssvscl
    syl22anc
    @41
    @21
    @27
    simpr
    hgmapvvlem2
    mpdan
    rexlimdv3a
    mpd
end
