include "cfv.mm"
include "clcd.mm"
include "csca.mm"
include "c0g.mm"
include "cv.mm"
include "wne.mm"
include "cbs.mm"
include "wrex.mm"
include "wceq.mm"
include "eqid.mm"
include "dvh1dim.mm"
include "wcel.mm"
include "w3a.mm"
include "chdma.mm"
include "wn.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr.mm"
include "hdmapeq0.mm"
include "biimpd.mm"
include "necon3ad.mm"
include "3impia.mm"
include "wi.mm"
include "cvsca.mm"
include "co.mm"
include "wo.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmod0vs.mm"
include "sylan.mm"
include "fveq2d.mm"
include "lmod0cl.mm"
include "syl.mm"
include "hgmapvs.mm"
include "hdmapval0.mm"
include "3eqtr3d.mm"
include "clvec.mm"
include "lcdlvec.mm"
include "hgmapdcl.mm"
include "hdmapcl.mm"
include "lvecvs0or.mm"
include "mpbid.mm"
include "orcomd.mm"
include "ord.mm"
include "3adant3.mm"
include "mpd.mm"
include "rexlimdv3a.mm"
include "lcd0.mm"
include "eqtrd.mm"

theorem hgmapval0
  let wph: wff ph
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  assume hgmapval0.h: |- H = ( LHyp ` K )
  assume hgmapval0.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapval0.r: |- R = ( Scalar ` U )
  assume hgmapval0.o: |- .0. = ( 0g ` R )
  assume hgmapval0.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmapval0.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ( G ` .0. ) = .0. )

  proof
    wph
    c.0
    cG
    cfv
    #
    cW
    cK
    clcd
    cfv
    cfv
    #
    csca
    cfv
    #
    c0g
    cfv
    #
    c.0
    wph
    vx
    cv
    #
    cU
    c0g
    cfv
    #
    wne
    #
    vx
    cU
    cbs
    cfv
    #
    wrex
    @0
    @3
    wceq
    #
    wph
    vx
    cU
    cH
    cK
    @7
    cW
    @5
    hgmapval0.h
    hgmapval0.u
    @7
    eqid
    #
    @5
    eqid
    #
    hgmapval0.k
    dvh1dim
    wph
    @6
    @8
    vx
    @7
    wph
    @4
    @7
    wcel
    #
    @6
    w3a
    @4
    cW
    cK
    chdma
    cfv
    cfv
    #
    cfv
    #
    @1
    c0g
    cfv
    #
    wceq
    #
    wn
    #
    @8
    wph
    @11
    @6
    @16
    wph
    @11
    wa
    #
    @15
    @4
    @5
    @17
    @15
    @4
    @5
    wceq
    @17
    @1
    @14
    @12
    @4
    cU
    cH
    cK
    @7
    cW
    @5
    hgmapval0.h
    hgmapval0.u
    @9
    @10
    @1
    eqid
    #
    @14
    eqid
    #
    @12
    eqid
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @11
    hgmapval0.k
    adantr
    #
    wph
    @11
    simpr
    #
    hdmapeq0
    biimpd
    necon3ad
    3impia
    wph
    @11
    @16
    @8
    wi
    @6
    @17
    @15
    @8
    @17
    @8
    @15
    @17
    @0
    @13
    @1
    cvsca
    cfv
    #
    co
    #
    @14
    wceq
    @8
    @15
    wo
    @17
    c.0
    @4
    cU
    cvsca
    cfv
    #
    co
    #
    @12
    cfv
    @5
    @12
    cfv
    #
    @24
    @14
    @17
    @26
    @5
    @12
    wph
    cU
    clmod
    wcel
    #
    @11
    @26
    @5
    wceq
    wph
    cU
    cH
    cK
    cW
    hgmapval0.h
    hgmapval0.u
    hgmapval0.k
    dvhlmod
    #
    @25
    cR
    c.0
    @7
    cU
    @4
    @5
    @9
    hgmapval0.r
    @25
    eqid
    #
    hgmapval0.o
    @10
    lmod0vs
    sylan
    fveq2d
    @17
    cR
    cbs
    cfv
    #
    @1
    cR
    @12
    @23
    @25
    cU
    c.0
    cG
    cH
    cK
    @7
    cW
    @4
    hgmapval0.h
    hgmapval0.u
    @9
    @30
    hgmapval0.r
    @31
    eqid
    #
    @18
    @23
    eqid
    #
    @20
    hgmapval0.g
    @21
    @22
    wph
    c.0
    @31
    wcel
    #
    @11
    wph
    @28
    @34
    @29
    cR
    @31
    cU
    c.0
    hgmapval0.r
    @32
    hgmapval0.o
    lmod0cl
    #
    syl
    adantr
    hgmapvs
    wph
    @27
    @14
    wceq
    @11
    wph
    @1
    @14
    @12
    cU
    cH
    cK
    cW
    @5
    hgmapval0.h
    hgmapval0.u
    @10
    @18
    @19
    @20
    hgmapval0.k
    hdmapval0
    adantr
    3eqtr3d
    @17
    @0
    @23
    @2
    @2
    cbs
    cfv
    #
    @3
    @1
    cbs
    cfv
    #
    @1
    @13
    @14
    @37
    eqid
    #
    @33
    @2
    eqid
    #
    @36
    eqid
    #
    @3
    eqid
    #
    @19
    wph
    @1
    clvec
    wcel
    @11
    wph
    @1
    cH
    cK
    cW
    hgmapval0.h
    @18
    hgmapval0.k
    lcdlvec
    adantr
    @17
    @36
    @31
    @1
    @2
    cR
    cU
    c.0
    cG
    cH
    cK
    cW
    hgmapval0.h
    hgmapval0.u
    hgmapval0.r
    @32
    @18
    @39
    @40
    hgmapval0.g
    @21
    @17
    @28
    @34
    @17
    cU
    cH
    cK
    cW
    hgmapval0.h
    hgmapval0.u
    @21
    dvhlmod
    @35
    syl
    hgmapdcl
    @17
    @1
    @37
    @12
    @4
    cU
    cH
    cK
    @7
    cW
    hgmapval0.h
    hgmapval0.u
    @9
    @18
    @38
    @20
    @21
    @22
    hdmapcl
    lvecvs0or
    mpbid
    orcomd
    ord
    3adant3
    mpd
    rexlimdv3a
    mpd
    wph
    @1
    @2
    cU
    cR
    cH
    cK
    @3
    cW
    c.0
    hgmapval0.h
    hgmapval0.u
    hgmapval0.r
    hgmapval0.o
    @18
    @39
    @41
    hgmapval0.k
    lcd0
    eqtrd
end
