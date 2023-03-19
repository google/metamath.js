include "cv.mm"
include "csn.mm"
include "cdvh.mm"
include "cfv.mm"
include "clspn.mm"
include "wcel.mm"
include "wn.mm"
include "cbs.mm"
include "wrex.mm"
include "wceq.mm"
include "eqid.mm"
include "c0g.mm"
include "cltrn.mm"
include "dvheveccl.mm"
include "eldifad.mm"
include "dvh2dim.mm"
include "w3a.mm"
include "clcd.mm"
include "chdma1.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "cun.mm"
include "ssid.mm"
include "unssi.mm"
include "sseli.mm"
include "con3i.mm"
include "3ad2ant3.mm"
include "hdmapeveclem.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hdmapevec
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cH: class H
  let cJ: class J
  let cK: class K
  let cW: class W
  let vz: setvar z
  assume hdmapevec.h: |- H = ( LHyp ` K )
  assume hdmapevec.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapevec.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmapevec.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapevec.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ( S ` E ) = ( J ` E ) )

  proof
    wph
    vz
    cv
    #
    cE
    csn
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clspn
    cfv
    #
    cfv
    #
    wcel
    #
    wn
    #
    vz
    @1
    cbs
    cfv
    #
    wrex
    cE
    cS
    cfv
    cE
    cJ
    cfv
    wceq
    #
    wph
    vz
    @1
    cH
    cK
    @2
    @6
    cW
    cE
    hdmapevec.h
    @1
    eqid
    #
    @6
    eqid
    #
    @2
    eqid
    #
    hdmapevec.k
    wph
    cE
    @6
    @1
    c0g
    cfv
    #
    csn
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
    @1
    cE
    cH
    cK
    @6
    cW
    @11
    hdmapevec.h
    @12
    eqid
    @13
    eqid
    @8
    @9
    @11
    eqid
    hdmapevec.e
    hdmapevec.k
    dvheveccl
    eldifad
    dvh2dim
    wph
    @5
    @7
    vz
    @6
    wph
    @0
    @6
    wcel
    #
    @5
    w3a
    cW
    cK
    clcd
    cfv
    cfv
    #
    @15
    cbs
    cfv
    #
    cS
    @1
    cE
    cH
    cW
    cK
    chdma1
    cfv
    cfv
    #
    cJ
    cK
    @2
    @6
    cW
    @0
    hdmapevec.h
    hdmapevec.e
    hdmapevec.j
    hdmapevec.s
    wph
    @14
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @5
    hdmapevec.k
    3ad2ant1
    @8
    @9
    @10
    @15
    eqid
    @16
    eqid
    @17
    eqid
    wph
    @14
    @5
    simp2
    @5
    wph
    @0
    @3
    @3
    cun
    #
    wcel
    #
    wn
    @14
    @19
    @4
    @18
    @3
    @0
    @3
    @3
    @3
    @3
    ssid
    #
    @20
    unssi
    sseli
    con3i
    3ad2ant3
    hdmapeveclem
    rexlimdv3a
    mpd
end
