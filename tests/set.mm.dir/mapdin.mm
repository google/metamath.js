include "cin.mm"
include "cfv.mm"
include "wss.mm"
include "inss1.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lssincl.mm"
include "syl3anc.mm"
include "mapdord.mm"
include "mpbiri.mm"
include "inss2.mm"
include "ssind.mm"
include "ccnv.mm"
include "clcd.mm"
include "eqid.mm"
include "clss.mm"
include "crn.mm"
include "mapdcl2.mm"
include "mapdrn2.mm"
include "eleqtrrd.mm"
include "mapdincl.mm"
include "mapdcnvid2.mm"
include "syl6eqss.mm"
include "lcdlmod.mm"
include "mapdcnvcl.mm"
include "mpbid.mm"
include "mpbird.mm"
include "eqsstr3d.mm"
include "eqssd.mm"

theorem mapdin
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mapdin.h: |- H = ( LHyp ` K )
  assume mapdin.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdin.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdin.s: |- S = ( LSubSp ` U )
  assume mapdin.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdin.x: |- ( ph -> X e. S )
  assume mapdin.y: |- ( ph -> Y e. S )


  assert |- ( ph -> ( M ` ( X i^i Y ) ) = ( ( M ` X ) i^i ( M ` Y ) ) )

  proof
    wph
    cX
    cY
    cin
    #
    cM
    cfv
    #
    cX
    cM
    cfv
    #
    cY
    cM
    cfv
    #
    cin
    #
    wph
    @1
    @2
    @3
    wph
    @1
    @2
    wss
    @0
    cX
    wss
    cX
    cY
    inss1
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    @0
    cX
    mapdin.h
    mapdin.u
    mapdin.s
    mapdin.m
    mapdin.k
    wph
    cU
    clmod
    wcel
    cX
    cS
    wcel
    cY
    cS
    wcel
    @0
    cS
    wcel
    wph
    cU
    cH
    cK
    cW
    mapdin.h
    mapdin.u
    mapdin.k
    dvhlmod
    mapdin.x
    mapdin.y
    cS
    cX
    cY
    cU
    mapdin.s
    lssincl
    syl3anc
    #
    mapdin.x
    mapdord
    mpbiri
    wph
    @1
    @3
    wss
    @0
    cY
    wss
    cX
    cY
    inss2
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    @0
    cY
    mapdin.h
    mapdin.u
    mapdin.s
    mapdin.m
    mapdin.k
    @5
    mapdin.y
    mapdord
    mpbiri
    ssind
    wph
    @4
    @4
    cM
    ccnv
    cfv
    #
    cM
    cfv
    #
    @1
    wph
    cH
    cK
    cM
    cW
    @4
    mapdin.h
    mapdin.m
    mapdin.k
    wph
    cW
    cK
    clcd
    cfv
    cfv
    #
    cU
    cH
    cK
    cM
    cW
    @2
    @3
    mapdin.h
    mapdin.m
    mapdin.u
    @8
    eqid
    #
    mapdin.k
    wph
    @2
    @8
    clss
    cfv
    #
    cM
    crn
    #
    wph
    @8
    cX
    cS
    @10
    cU
    cH
    cK
    cM
    cW
    mapdin.h
    mapdin.m
    mapdin.u
    mapdin.s
    @9
    @10
    eqid
    #
    mapdin.k
    mapdin.x
    mapdcl2
    #
    wph
    @8
    @10
    cH
    cK
    cM
    cW
    mapdin.h
    mapdin.m
    @9
    @12
    mapdin.k
    mapdrn2
    #
    eleqtrrd
    wph
    @3
    @10
    @11
    wph
    @8
    cY
    cS
    @10
    cU
    cH
    cK
    cM
    cW
    mapdin.h
    mapdin.m
    mapdin.u
    mapdin.s
    @9
    @12
    mapdin.k
    mapdin.y
    mapdcl2
    #
    @14
    eleqtrrd
    mapdincl
    mapdcnvid2
    #
    wph
    @7
    @1
    wss
    @6
    @0
    wss
    wph
    @6
    cX
    cY
    wph
    @7
    @2
    wss
    @6
    cX
    wss
    wph
    @7
    @4
    @2
    @16
    @2
    @3
    inss1
    syl6eqss
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    @6
    cX
    mapdin.h
    mapdin.u
    mapdin.s
    mapdin.m
    mapdin.k
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    @4
    mapdin.h
    mapdin.m
    mapdin.u
    mapdin.s
    mapdin.k
    wph
    @4
    @10
    @11
    wph
    @8
    clmod
    wcel
    @2
    @10
    wcel
    @3
    @10
    wcel
    @4
    @10
    wcel
    wph
    @8
    cH
    cK
    cW
    mapdin.h
    @9
    mapdin.k
    lcdlmod
    @13
    @15
    @10
    @2
    @3
    @8
    @12
    lssincl
    syl3anc
    @14
    eleqtrrd
    #
    mapdcnvcl
    #
    mapdin.x
    mapdord
    mpbid
    wph
    @7
    @3
    wss
    @6
    cY
    wss
    wph
    @7
    @4
    @3
    wph
    cH
    cK
    cM
    cW
    @4
    mapdin.h
    mapdin.m
    mapdin.k
    @17
    mapdcnvid2
    @2
    @3
    inss2
    syl6eqss
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    @6
    cY
    mapdin.h
    mapdin.u
    mapdin.s
    mapdin.m
    mapdin.k
    @18
    mapdin.y
    mapdord
    mpbid
    ssind
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    @6
    @0
    mapdin.h
    mapdin.u
    mapdin.s
    mapdin.m
    mapdin.k
    @18
    @5
    mapdord
    mpbird
    eqsstr3d
    eqssd
end
