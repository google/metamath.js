include "crn.mm"
include "clcd.mm"
include "cfv.mm"
include "csca.mm"
include "cbs.mm"
include "wfn.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "hgmapfnN.mm"
include "wa.mm"
include "eqid.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr.mm"
include "hgmapdcl.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "c0g.mm"
include "chdma.mm"
include "cvsca.mm"
include "hgmaprnlem5N.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "lcdsbase.mm"
include "eqtrd.mm"

theorem hgmaprnN
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vz: setvar z
  assume hgmaprn.h: |- H = ( LHyp ` K )
  assume hgmaprn.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmaprn.r: |- R = ( Scalar ` U )
  assume hgmaprn.b: |- B = ( Base ` R )
  assume hgmaprn.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmaprn.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ran G = B )

  proof
    wph
    cG
    crn
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
    cbs
    cfv
    #
    cB
    wph
    @0
    @3
    wph
    cG
    cB
    wfn
    vz
    cv
    #
    cG
    cfv
    @3
    wcel
    #
    vz
    cB
    wral
    @0
    @3
    wss
    wph
    cB
    cR
    cU
    cG
    cH
    cK
    cW
    hgmaprn.h
    hgmaprn.u
    hgmaprn.r
    hgmaprn.b
    hgmaprn.g
    hgmaprn.k
    hgmapfnN
    wph
    @5
    vz
    cB
    wph
    @4
    cB
    wcel
    #
    wa
    @3
    cB
    @1
    @2
    cR
    cU
    @4
    cG
    cH
    cK
    cW
    hgmaprn.h
    hgmaprn.u
    hgmaprn.r
    hgmaprn.b
    @1
    eqid
    #
    @2
    eqid
    #
    @3
    eqid
    #
    hgmaprn.g
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @6
    hgmaprn.k
    adantr
    wph
    @6
    simpr
    hgmapdcl
    ralrimiva
    vz
    cB
    @3
    cG
    fnfvrnss
    syl2anc
    wph
    vz
    @3
    @0
    wph
    @4
    @3
    wcel
    #
    @4
    @0
    wcel
    wph
    @11
    wa
    vz
    @3
    cB
    @1
    @1
    cbs
    cfv
    #
    @2
    @1
    c0g
    cfv
    #
    cR
    cW
    cK
    chdma
    cfv
    cfv
    #
    @1
    cvsca
    cfv
    #
    cU
    cvsca
    cfv
    #
    cU
    cG
    cH
    cK
    cU
    cbs
    cfv
    #
    cW
    cU
    c0g
    cfv
    #
    hgmaprn.h
    hgmaprn.u
    @17
    eqid
    hgmaprn.r
    hgmaprn.b
    @16
    eqid
    @18
    eqid
    @7
    @12
    eqid
    @8
    @9
    @15
    eqid
    @13
    eqid
    @14
    eqid
    hgmaprn.g
    wph
    @10
    @11
    hgmaprn.k
    adantr
    wph
    @11
    simpr
    hgmaprnlem5N
    ex
    ssrdv
    eqssd
    wph
    @1
    @3
    @2
    cU
    cR
    cH
    cK
    cB
    cW
    hgmaprn.h
    hgmaprn.u
    hgmaprn.r
    hgmaprn.b
    @7
    @8
    @9
    hgmaprn.k
    lcdsbase
    eqtrd
end
