include "cv.mm"
include "c0g.mm"
include "cfv.mm"
include "wne.mm"
include "cbs.mm"
include "wrex.mm"
include "wceq.mm"
include "eqid.mm"
include "dvh1dim.mm"
include "wcel.mm"
include "w3a.mm"
include "chdma.mm"
include "clcd.mm"
include "cvsca.mm"
include "co.mm"
include "csca.mm"
include "cur.mm"
include "lcd1.mm"
include "oveq1d.mm"
include "3ad2ant1.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "chlt.mm"
include "wa.mm"
include "simp2.mm"
include "hdmapcl.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "dvhlmod.mm"
include "fveq2d.mm"
include "crg.mm"
include "lmodring.mm"
include "ringidcl.mm"
include "3syl.mm"
include "hgmapvs.mm"
include "3eqtr2rd.mm"
include "clvec.mm"
include "lcdlvec.mm"
include "hgmapcl.mm"
include "lcdsbase.mm"
include "eleqtrrd.mm"
include "simp3.mm"
include "hdmapeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "lvecvscan2.mm"
include "mpbid.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hgmapval1
  let wph: wff ph
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume hgmapval1.h: |- H = ( LHyp ` K )
  assume hgmapval1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapval1.r: |- R = ( Scalar ` U )
  assume hgmapval1.i: |- .1. = ( 1r ` R )
  assume hgmapval1.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmapval1.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ( G ` .1. ) = .1. )

  proof
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
    c.1
    cG
    cfv
    #
    c.1
    wceq
    #
    wph
    vx
    cU
    cH
    cK
    @3
    cW
    @1
    hgmapval1.h
    hgmapval1.u
    @3
    eqid
    #
    @1
    eqid
    #
    hgmapval1.k
    dvh1dim
    wph
    @2
    @5
    vx
    @3
    wph
    @0
    @3
    wcel
    #
    @2
    w3a
    #
    @4
    @0
    cW
    cK
    chdma
    cfv
    cfv
    #
    cfv
    #
    cW
    cK
    clcd
    cfv
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    c.1
    @11
    @13
    co
    #
    wceq
    @5
    @9
    @15
    @11
    c.1
    @0
    cU
    cvsca
    cfv
    #
    co
    #
    @10
    cfv
    @14
    @9
    @12
    csca
    cfv
    #
    cur
    cfv
    #
    @11
    @13
    co
    #
    @15
    @11
    wph
    @8
    @20
    @15
    wceq
    @2
    wph
    @19
    c.1
    @11
    @13
    wph
    @12
    @18
    cU
    c.1
    cR
    cH
    @19
    cK
    cW
    hgmapval1.h
    hgmapval1.u
    hgmapval1.r
    hgmapval1.i
    @12
    eqid
    #
    @18
    eqid
    #
    @19
    eqid
    #
    hgmapval1.k
    lcd1
    oveq1d
    3ad2ant1
    @9
    @12
    clmod
    wcel
    #
    @11
    @12
    cbs
    cfv
    #
    wcel
    @20
    @11
    wceq
    wph
    @8
    @24
    @2
    wph
    @12
    cH
    cK
    cW
    hgmapval1.h
    @21
    hgmapval1.k
    lcdlmod
    3ad2ant1
    @9
    @12
    @25
    @10
    @0
    cU
    cH
    cK
    @3
    cW
    hgmapval1.h
    hgmapval1.u
    @6
    @21
    @25
    eqid
    #
    @10
    eqid
    #
    wph
    @8
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @2
    hgmapval1.k
    3ad2ant1
    #
    wph
    @8
    @2
    simp2
    #
    hdmapcl
    #
    @13
    @19
    @18
    @25
    @12
    @11
    @26
    @22
    @13
    eqid
    #
    @23
    lmodvs1
    syl2anc
    eqtr3d
    @9
    @17
    @0
    @10
    @9
    cU
    clmod
    wcel
    #
    @8
    @17
    @0
    wceq
    wph
    @8
    @32
    @2
    wph
    cU
    cH
    cK
    cW
    hgmapval1.h
    hgmapval1.u
    hgmapval1.k
    dvhlmod
    #
    3ad2ant1
    @29
    @16
    c.1
    cR
    @3
    cU
    @0
    @6
    hgmapval1.r
    @16
    eqid
    #
    hgmapval1.i
    lmodvs1
    syl2anc
    fveq2d
    @9
    cR
    cbs
    cfv
    #
    @12
    cR
    @10
    @13
    @16
    cU
    c.1
    cG
    cH
    cK
    @3
    cW
    @0
    hgmapval1.h
    hgmapval1.u
    @6
    @34
    hgmapval1.r
    @35
    eqid
    #
    @21
    @31
    @27
    hgmapval1.g
    @28
    @29
    wph
    @8
    c.1
    @35
    wcel
    #
    @2
    wph
    @32
    cR
    crg
    wcel
    @37
    @33
    cR
    cU
    hgmapval1.r
    lmodring
    @35
    cR
    c.1
    @36
    hgmapval1.i
    ringidcl
    3syl
    #
    3ad2ant1
    hgmapvs
    3eqtr2rd
    @9
    @4
    c.1
    @13
    @18
    @18
    cbs
    cfv
    #
    @25
    @12
    @11
    @12
    c0g
    cfv
    #
    @26
    @31
    @22
    @39
    eqid
    #
    @40
    eqid
    #
    wph
    @8
    @12
    clvec
    wcel
    @2
    wph
    @12
    cH
    cK
    cW
    hgmapval1.h
    @21
    hgmapval1.k
    lcdlvec
    3ad2ant1
    wph
    @8
    @4
    @39
    wcel
    @2
    wph
    @4
    @35
    @39
    wph
    @35
    cR
    cU
    c.1
    cG
    cH
    cK
    cW
    hgmapval1.h
    hgmapval1.u
    hgmapval1.r
    @36
    hgmapval1.g
    hgmapval1.k
    @38
    hgmapcl
    wph
    @12
    @39
    @18
    cU
    cR
    cH
    cK
    @35
    cW
    hgmapval1.h
    hgmapval1.u
    hgmapval1.r
    @36
    @21
    @22
    @41
    hgmapval1.k
    lcdsbase
    #
    eleqtrrd
    3ad2ant1
    wph
    @8
    c.1
    @39
    wcel
    @2
    wph
    c.1
    @35
    @39
    @38
    @43
    eleqtrrd
    3ad2ant1
    @30
    @9
    @11
    @40
    wne
    @2
    wph
    @8
    @2
    simp3
    @9
    @11
    @40
    @0
    @1
    @9
    @12
    @40
    @10
    @0
    cU
    cH
    cK
    @3
    cW
    @1
    hgmapval1.h
    hgmapval1.u
    @6
    @7
    @21
    @42
    @27
    @28
    @29
    hdmapeq0
    necon3bid
    mpbird
    lvecvscan2
    mpbid
    rexlimdv3a
    mpd
end
