include "cv.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "cltrn.mm"
include "cop.mm"
include "cpr.mm"
include "clspn.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "wceq.mm"
include "eqid.mm"
include "csn.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmod0vcl.mm"
include "syl.mm"
include "dvh3dim.mm"
include "w3a.mm"
include "chvm.mm"
include "cotp.mm"
include "chdma1.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "cun.mm"
include "wi.mm"
include "clss.mm"
include "lspprcl.mm"
include "lspprid1.mm"
include "lspsnel5a.mm"
include "lspprid2.mm"
include "unssd.mm"
include "ssneld.mm"
include "adantr.mm"
include "3impia.mm"
include "hdmapval2.mm"
include "cmpd.mm"
include "hvmapcl2.mm"
include "mapdhvmap.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "simp3.mm"
include "lspindpi.mm"
include "simpld.mm"
include "necomd.mm"
include "cdif.mm"
include "hdmap1cl.mm"
include "hdmap1val0.mm"
include "eqtrd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hdmapval0
  let wph: wff ph
  let cC: class C
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  assume hdmapval0.h: |- H = ( LHyp ` K )
  assume hdmapval0.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapval0.o: |- .0. = ( 0g ` U )
  assume hdmapval0.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmapval0.q: |- Q = ( 0g ` C )
  assume hdmapval0.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapval0.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ( S ` .0. ) = Q )

  proof
    wph
    vx
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
    c.0
    cpr
    cU
    clspn
    cfv
    #
    cfv
    #
    wcel
    wn
    #
    vx
    cU
    cbs
    cfv
    #
    wrex
    c.0
    cS
    cfv
    #
    cQ
    wceq
    #
    wph
    vx
    cU
    cH
    cK
    @4
    @7
    cW
    @3
    c.0
    hdmapval0.h
    hdmapval0.u
    @7
    eqid
    #
    @4
    eqid
    #
    hdmapval0.k
    wph
    @3
    @7
    c.0
    csn
    #
    wph
    @1
    @2
    cU
    @3
    cH
    cK
    @7
    cW
    c.0
    hdmapval0.h
    @1
    eqid
    @2
    eqid
    hdmapval0.u
    @10
    hdmapval0.o
    @3
    eqid
    #
    hdmapval0.k
    dvheveccl
    #
    eldifad
    #
    wph
    cU
    clmod
    wcel
    c.0
    @7
    wcel
    #
    wph
    cU
    cH
    cK
    cW
    hdmapval0.h
    hdmapval0.u
    hdmapval0.k
    dvhlmod
    #
    @7
    cU
    c.0
    @10
    hdmapval0.o
    lmod0vcl
    syl
    #
    dvh3dim
    wph
    @6
    @9
    vx
    @7
    wph
    @0
    @7
    wcel
    #
    @6
    w3a
    #
    @8
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
    #
    c.0
    cotp
    @23
    cfv
    cQ
    @20
    cC
    cC
    cbs
    cfv
    #
    cS
    c.0
    cU
    @3
    cH
    @23
    @21
    cK
    @4
    @7
    cW
    @0
    hdmapval0.h
    @13
    hdmapval0.u
    @10
    @11
    hdmapval0.c
    @25
    eqid
    #
    @21
    eqid
    #
    @23
    eqid
    #
    hdmapval0.s
    wph
    @19
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @6
    hdmapval0.k
    3ad2ant1
    #
    wph
    @19
    @16
    @6
    @18
    3ad2ant1
    #
    wph
    @19
    @6
    simp2
    #
    wph
    @19
    @6
    @0
    @3
    csn
    @4
    cfv
    #
    @12
    @4
    cfv
    #
    cun
    #
    wcel
    wn
    #
    wph
    @6
    @35
    wi
    @19
    wph
    @34
    @5
    @0
    wph
    @32
    @33
    @5
    wph
    cU
    clss
    cfv
    #
    @5
    @4
    cU
    @3
    @36
    eqid
    #
    @11
    @17
    wph
    @36
    @4
    @7
    cU
    @3
    c.0
    @10
    @37
    @11
    @17
    @15
    @18
    lspprcl
    #
    wph
    @4
    @7
    cU
    @3
    c.0
    @10
    @11
    @17
    @15
    @18
    lspprid1
    lspsnel5a
    wph
    @36
    @5
    @4
    cU
    c.0
    @37
    @11
    @17
    @38
    wph
    @4
    @7
    cU
    @3
    c.0
    @10
    @11
    @17
    @15
    @18
    lspprid2
    lspsnel5a
    unssd
    ssneld
    adantr
    3impia
    hdmapval2
    @20
    cC
    @25
    cQ
    cU
    @24
    cH
    @23
    cK
    @7
    cW
    @0
    c.0
    hdmapval0.h
    hdmapval0.u
    @10
    hdmapval0.o
    hdmapval0.c
    @26
    hdmapval0.q
    @28
    @29
    @20
    cC
    @25
    cU
    @22
    cH
    @23
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
    @7
    cW
    @3
    @0
    c.0
    hdmapval0.h
    hdmapval0.u
    @10
    hdmapval0.o
    @11
    hdmapval0.c
    @26
    @39
    eqid
    #
    @40
    eqid
    #
    @28
    @29
    wph
    @19
    @22
    @25
    wcel
    @6
    wph
    @22
    @25
    cQ
    csn
    wph
    cC
    cU
    @25
    cH
    cK
    @21
    cQ
    @7
    cW
    @3
    c.0
    hdmapval0.h
    hdmapval0.u
    @10
    hdmapval0.o
    hdmapval0.c
    @26
    hdmapval0.q
    @27
    hdmapval0.k
    @14
    hvmapcl2
    eldifad
    3ad2ant1
    wph
    @19
    @32
    @40
    cfv
    @22
    csn
    @39
    cfv
    wceq
    @6
    wph
    cC
    @21
    cU
    cH
    @39
    cK
    @40
    @4
    @7
    cW
    @3
    c.0
    hdmapval0.h
    hdmapval0.u
    @10
    hdmapval0.o
    @11
    hdmapval0.c
    @41
    @42
    @27
    hdmapval0.k
    @14
    mapdhvmap
    3ad2ant1
    @20
    @0
    csn
    @4
    cfv
    #
    @32
    @20
    @43
    @32
    wne
    @43
    @33
    wne
    @20
    @4
    @7
    cU
    @0
    @3
    c.0
    @10
    @11
    wph
    @19
    cU
    clvec
    wcel
    @6
    wph
    cU
    cH
    cK
    cW
    hdmapval0.h
    hdmapval0.u
    hdmapval0.k
    dvhlvec
    3ad2ant1
    @31
    wph
    @19
    @3
    @7
    wcel
    @6
    @15
    3ad2ant1
    @30
    wph
    @19
    @6
    simp3
    lspindpi
    simpld
    necomd
    wph
    @19
    @3
    @7
    @12
    cdif
    wcel
    @6
    @14
    3ad2ant1
    @31
    hdmap1cl
    @31
    hdmap1val0
    eqtrd
    rexlimdv3a
    mpd
end
