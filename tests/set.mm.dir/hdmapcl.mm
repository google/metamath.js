include "cfv.mm"
include "cv.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "cltrn.mm"
include "cop.mm"
include "csn.mm"
include "clspn.mm"
include "cun.mm"
include "wcel.mm"
include "wn.mm"
include "chvm.mm"
include "cotp.mm"
include "chdma1.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "chlt.mm"
include "eqid.mm"
include "hdmapval.mm"
include "wreu.mm"
include "cmpd.mm"
include "c0g.mm"
include "dvheveccl.mm"
include "mapdhvmap.mm"
include "hvmapcl2.mm"
include "eldifad.mm"
include "hdmap1eu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem hdmapcl
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vh: setvar h
  let vy: setvar y
  assume hdmapcl.h: |- H = ( LHyp ` K )
  assume hdmapcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapcl.v: |- V = ( Base ` U )
  assume hdmapcl.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapcl.d: |- D = ( Base ` C )
  assume hdmapcl.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapcl.t: |- ( ph -> T e. V )


  assert |- ( ph -> ( S ` T ) e. D )

  proof
    wph
    cT
    cS
    cfv
    vy
    cv
    #
    cid
    cK
    cbs
    cfv
    #
    cres
    cid
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cres
    cop
    #
    csn
    cU
    clspn
    cfv
    #
    cfv
    cT
    csn
    @4
    cfv
    cun
    wcel
    wn
    vh
    cv
    @0
    @3
    @3
    cW
    cK
    chvm
    cfv
    cfv
    #
    cfv
    #
    @0
    cotp
    cW
    cK
    chdma1
    cfv
    cfv
    #
    cfv
    cT
    cotp
    @7
    cfv
    wceq
    wi
    vy
    cV
    wral
    #
    vh
    cD
    crio
    #
    cD
    wph
    vh
    vy
    chlt
    cC
    cD
    cS
    cT
    cU
    @3
    cH
    @7
    @5
    cK
    @4
    cV
    cW
    hdmapcl.h
    @3
    eqid
    #
    hdmapcl.u
    hdmapcl.v
    @4
    eqid
    #
    hdmapcl.c
    hdmapcl.d
    @5
    eqid
    #
    @7
    eqid
    #
    hdmapcl.s
    hdmapcl.k
    hdmapcl.t
    hdmapval
    wph
    @8
    vh
    cD
    wreu
    @9
    cD
    wcel
    wph
    vh
    vy
    cC
    cD
    cT
    cU
    @6
    cH
    @7
    cK
    cC
    clspn
    cfv
    #
    cW
    cK
    cmpd
    cfv
    cfv
    #
    @4
    cV
    cW
    @3
    cU
    c0g
    cfv
    #
    hdmapcl.h
    hdmapcl.u
    hdmapcl.v
    @16
    eqid
    #
    @11
    hdmapcl.c
    hdmapcl.d
    @14
    eqid
    #
    @15
    eqid
    #
    @13
    hdmapcl.k
    wph
    cC
    @5
    cU
    cH
    @14
    cK
    @15
    @4
    cV
    cW
    @3
    @16
    hdmapcl.h
    hdmapcl.u
    hdmapcl.v
    @17
    @11
    hdmapcl.c
    @18
    @19
    @12
    hdmapcl.k
    wph
    @1
    @2
    cU
    @3
    cH
    cK
    cV
    cW
    @16
    hdmapcl.h
    @1
    eqid
    @2
    eqid
    hdmapcl.u
    hdmapcl.v
    @17
    @10
    hdmapcl.k
    dvheveccl
    #
    mapdhvmap
    @20
    wph
    @6
    cD
    cC
    c0g
    cfv
    #
    csn
    wph
    cC
    cU
    cD
    cH
    cK
    @5
    @21
    cV
    cW
    @3
    @16
    hdmapcl.h
    hdmapcl.u
    hdmapcl.v
    @17
    hdmapcl.c
    hdmapcl.d
    @21
    eqid
    @12
    hdmapcl.k
    @20
    hvmapcl2
    eldifad
    hdmapcl.t
    hdmap1eu
    @8
    vh
    cD
    riotacl
    syl
    eqeltrd
end
