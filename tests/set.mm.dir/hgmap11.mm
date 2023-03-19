include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "c0g.mm"
include "wne.mm"
include "cbs.mm"
include "wrex.mm"
include "eqid.mm"
include "dvh1dim.mm"
include "adantr.mm"
include "wcel.mm"
include "w3a.mm"
include "cvsca.mm"
include "co.mm"
include "chdma.mm"
include "clcd.mm"
include "simp1r.mm"
include "oveq1d.mm"
include "chlt.mm"
include "simp1l.mm"
include "syl.mm"
include "simp2.mm"
include "hgmapvs.mm"
include "3eqtr4d.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "hdmap11.mm"
include "mpbid.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "simp3.mm"
include "lvecvscan2.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "ex.mm"
include "fveq2.mm"
include "impbid1.mm"

theorem hgmap11
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let vt: setvar t
  assume hgmap11.h: |- H = ( LHyp ` K )
  assume hgmap11.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmap11.r: |- R = ( Scalar ` U )
  assume hgmap11.b: |- B = ( Base ` R )
  assume hgmap11.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmap11.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hgmap11.x: |- ( ph -> X e. B )
  assume hgmap11.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( G ` X ) = ( G ` Y ) <-> X = Y ) )

  proof
    wph
    cX
    cG
    cfv
    #
    cY
    cG
    cfv
    #
    wceq
    #
    cX
    cY
    wceq
    #
    wph
    @2
    @3
    wph
    @2
    wa
    #
    vt
    cv
    #
    cU
    c0g
    cfv
    #
    wne
    #
    vt
    cU
    cbs
    cfv
    #
    wrex
    #
    @3
    wph
    @9
    @2
    wph
    vt
    cU
    cH
    cK
    @8
    cW
    @6
    hgmap11.h
    hgmap11.u
    @8
    eqid
    #
    @6
    eqid
    #
    hgmap11.k
    dvh1dim
    adantr
    @4
    @7
    @3
    vt
    @8
    @4
    @5
    @8
    wcel
    #
    @7
    w3a
    #
    cX
    @5
    cU
    cvsca
    cfv
    #
    co
    #
    cY
    @5
    @14
    co
    #
    wceq
    #
    @3
    @13
    @15
    cW
    cK
    chdma
    cfv
    cfv
    #
    cfv
    #
    @16
    @18
    cfv
    #
    wceq
    @17
    @13
    @0
    @5
    @18
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
    @1
    @21
    @23
    co
    @19
    @20
    @13
    @0
    @1
    @21
    @23
    wph
    @2
    @12
    @7
    simp1r
    oveq1d
    @13
    cB
    @22
    cR
    @18
    @23
    @14
    cU
    cX
    cG
    cH
    cK
    @8
    cW
    @5
    hgmap11.h
    hgmap11.u
    @10
    @14
    eqid
    #
    hgmap11.r
    hgmap11.b
    @22
    eqid
    #
    @23
    eqid
    #
    @18
    eqid
    #
    hgmap11.g
    @13
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    wph
    @2
    @12
    @7
    simp1l
    #
    hgmap11.k
    syl
    #
    @4
    @12
    @7
    simp2
    #
    @13
    wph
    cX
    cB
    wcel
    #
    @28
    hgmap11.x
    syl
    #
    hgmapvs
    @13
    cB
    @22
    cR
    @18
    @23
    @14
    cU
    cY
    cG
    cH
    cK
    @8
    cW
    @5
    hgmap11.h
    hgmap11.u
    @10
    @24
    hgmap11.r
    hgmap11.b
    @25
    @26
    @27
    hgmap11.g
    @29
    @30
    @13
    wph
    cY
    cB
    wcel
    #
    @28
    hgmap11.y
    syl
    #
    hgmapvs
    3eqtr4d
    @13
    @18
    cU
    cH
    cK
    @8
    cW
    @15
    @16
    hgmap11.h
    hgmap11.u
    @10
    @27
    @29
    @13
    cU
    clmod
    wcel
    #
    @31
    @12
    @15
    @8
    wcel
    @13
    wph
    @35
    @28
    wph
    cU
    cH
    cK
    cW
    hgmap11.h
    hgmap11.u
    hgmap11.k
    dvhlmod
    syl
    #
    @32
    @30
    cX
    @14
    cR
    cB
    @8
    cU
    @5
    @10
    hgmap11.r
    @24
    hgmap11.b
    lmodvscl
    syl3anc
    @13
    @35
    @33
    @12
    @16
    @8
    wcel
    @36
    @34
    @30
    cY
    @14
    cR
    cB
    @8
    cU
    @5
    @10
    hgmap11.r
    @24
    hgmap11.b
    lmodvscl
    syl3anc
    hdmap11
    mpbid
    @13
    cX
    cY
    @14
    cR
    cB
    @8
    cU
    @5
    @6
    @10
    @24
    hgmap11.r
    hgmap11.b
    @11
    @13
    wph
    cU
    clvec
    wcel
    @28
    wph
    cU
    cH
    cK
    cW
    hgmap11.h
    hgmap11.u
    hgmap11.k
    dvhlvec
    syl
    @32
    @34
    @30
    @4
    @12
    @7
    simp3
    lvecvscan2
    mpbid
    rexlimdv3a
    mpd
    ex
    cX
    cY
    cG
    fveq2
    impbid1
end
