include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "coch.mm"
include "wcel.mm"
include "eqid.mm"
include "chlt.mm"
include "adantr.mm"
include "cdif.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "dochnel.mm"
include "wi.mm"
include "clk.mm"
include "clfn.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "clcd.mm"
include "cbs.mm"
include "hdmapcl.mm"
include "lcdvbaselfl.mm"
include "ellkr2.mm"
include "biimpar.mm"
include "hdmaplkr.mm"
include "eleqtrd.mm"
include "ex.mm"
include "mtod.mm"
include "neqned.mm"
include "necon4d.mm"
include "imp.mm"
include "fveq2.mm"
include "lfl0.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "impbida.mm"

theorem hdmapip0
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  assume hdmapip0.h: |- H = ( LHyp ` K )
  assume hdmapip0.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapip0.v: |- V = ( Base ` U )
  assume hdmapip0.o: |- .0. = ( 0g ` U )
  assume hdmapip0.r: |- R = ( Scalar ` U )
  assume hdmapip0.z: |- Z = ( 0g ` R )
  assume hdmapip0.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapip0.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapip0.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( ( S ` X ) ` X ) = Z <-> X = .0. ) )

  proof
    wph
    cX
    cX
    cS
    cfv
    #
    cfv
    #
    cZ
    wceq
    #
    cX
    c.0
    wceq
    #
    wph
    @2
    @3
    wph
    cX
    c.0
    @1
    cZ
    wph
    cX
    c.0
    wne
    #
    @1
    cZ
    wne
    wph
    @4
    wa
    #
    @1
    cZ
    @5
    @2
    cX
    cX
    csn
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    #
    wcel
    #
    @5
    cU
    cH
    cK
    @6
    cV
    cW
    cX
    c.0
    hdmapip0.h
    @6
    eqid
    #
    hdmapip0.u
    hdmapip0.v
    hdmapip0.o
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @4
    hdmapip0.k
    adantr
    @5
    cX
    cV
    wcel
    #
    @4
    wa
    cX
    cV
    c.0
    csn
    cdif
    wcel
    wph
    @10
    @4
    hdmapip0.x
    anim1i
    cX
    cV
    c.0
    eldifsn
    sylibr
    dochnel
    wph
    @2
    @8
    wi
    @4
    wph
    @2
    @8
    wph
    @2
    wa
    cX
    @0
    cU
    clk
    cfv
    #
    cfv
    #
    @7
    wph
    cX
    @12
    wcel
    @2
    wph
    cR
    cU
    clfn
    cfv
    #
    @0
    @11
    cV
    cU
    cX
    clmod
    cZ
    hdmapip0.v
    hdmapip0.r
    hdmapip0.z
    @13
    eqid
    #
    @11
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    hdmapip0.h
    hdmapip0.u
    hdmapip0.k
    dvhlmod
    #
    wph
    cW
    cK
    clcd
    cfv
    cfv
    #
    cU
    @13
    cH
    cK
    @17
    cbs
    cfv
    #
    cW
    @0
    hdmapip0.h
    @17
    eqid
    #
    @18
    eqid
    #
    hdmapip0.u
    @14
    hdmapip0.k
    wph
    @17
    @18
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    hdmapip0.h
    hdmapip0.u
    hdmapip0.v
    @19
    @20
    hdmapip0.s
    hdmapip0.k
    hdmapip0.x
    hdmapcl
    lcdvbaselfl
    #
    hdmapip0.x
    ellkr2
    biimpar
    wph
    @12
    @7
    wceq
    @2
    wph
    cS
    cU
    @13
    cH
    cK
    @6
    cV
    cW
    cX
    @11
    hdmapip0.h
    @9
    hdmapip0.u
    hdmapip0.v
    @14
    @15
    hdmapip0.s
    hdmapip0.k
    hdmapip0.x
    hdmaplkr
    adantr
    eleqtrd
    ex
    adantr
    mtod
    neqned
    ex
    necon4d
    imp
    @3
    wph
    @1
    c.0
    @0
    cfv
    #
    cZ
    cX
    c.0
    @0
    fveq2
    wph
    cU
    clmod
    wcel
    @0
    @13
    wcel
    @22
    cZ
    wceq
    @16
    @21
    cR
    @13
    @0
    cU
    cZ
    c.0
    hdmapip0.r
    hdmapip0.z
    hdmapip0.o
    @14
    lfl0
    syl2anc
    sylan9eqr
    impbida
end
