include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wb.mm"
include "clss.mm"
include "eqid.mm"
include "chlt.mm"
include "cbs.mm"
include "wss.mm"
include "dvhlmod.mm"
include "lshplss.mm"
include "lssss.mm"
include "syl.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "dochsatshpb.mm"
include "mpbird.mm"
include "wn.mm"
include "c0g.mm"
include "csn.mm"
include "clmod.mm"
include "lsatn0.mm"
include "neneqd.mm"
include "doch0.mm"
include "eqeq2d.mm"
include "cdih.mm"
include "crn.mm"
include "dochcl.mm"
include "dih0rn.mm"
include "doch11.mm"
include "bitr3d.mm"
include "mtbird.mm"
include "dochshpncl.mm"
include "necon1bbid.mm"
include "mpbid.mm"
include "impbida.mm"

theorem dochshpsat
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dochshpsat.h: |- H = ( LHyp ` K )
  assume dochshpsat.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochshpsat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochshpsat.a: |- A = ( LSAtoms ` U )
  assume dochshpsat.y: |- Y = ( LSHyp ` U )
  assume dochshpsat.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochshpsat.x: |- ( ph -> X e. Y )


  assert |- ( ph -> ( ( ._|_ ` ( ._|_ ` X ) ) = X <-> ( ._|_ ` X ) e. A ) )

  proof
    wph
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cX
    wceq
    #
    @0
    cA
    wcel
    #
    wph
    @2
    wa
    #
    @3
    @1
    cY
    wcel
    #
    @4
    @1
    cX
    cY
    wph
    @2
    simpr
    wph
    cX
    cY
    wcel
    @2
    dochshpsat.x
    adantr
    eqeltrd
    wph
    @3
    @5
    wb
    @2
    wph
    cA
    @0
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    c.pe
    cW
    cY
    dochshpsat.h
    dochshpsat.o
    dochshpsat.u
    @6
    eqid
    #
    dochshpsat.a
    dochshpsat.y
    dochshpsat.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cU
    cbs
    cfv
    #
    wss
    #
    @0
    @6
    wcel
    dochshpsat.k
    wph
    cX
    @6
    wcel
    @10
    wph
    @6
    cX
    cY
    cU
    @7
    dochshpsat.y
    wph
    cU
    cH
    cK
    cW
    dochshpsat.h
    dochshpsat.u
    dochshpsat.k
    dvhlmod
    #
    dochshpsat.x
    lshplss
    @6
    cX
    @9
    cU
    @9
    eqid
    #
    @7
    lssss
    syl
    #
    @6
    cU
    cH
    cK
    c.pe
    @9
    cW
    cX
    dochshpsat.h
    dochshpsat.u
    @12
    @7
    dochshpsat.o
    dochlss
    syl2anc
    dochsatshpb
    adantr
    mpbird
    wph
    @3
    wa
    #
    @1
    @9
    wceq
    #
    wn
    #
    @2
    @14
    @15
    @0
    cU
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    @14
    @0
    @18
    @14
    cA
    @0
    cU
    @17
    @17
    eqid
    #
    dochshpsat.a
    wph
    cU
    clmod
    wcel
    @3
    @11
    adantr
    wph
    @3
    simpr
    lsatn0
    neneqd
    @14
    @1
    @18
    c.pe
    cfv
    #
    wceq
    #
    @15
    @19
    @14
    @21
    @9
    @1
    @14
    @8
    @21
    @9
    wceq
    wph
    @8
    @3
    dochshpsat.k
    adantr
    cU
    cH
    cK
    c.pe
    @9
    cW
    @17
    dochshpsat.h
    dochshpsat.u
    dochshpsat.o
    @12
    @20
    doch0
    syl
    eqeq2d
    wph
    @22
    @19
    wb
    @3
    wph
    cH
    cW
    cK
    cdih
    cfv
    cfv
    #
    cK
    c.pe
    cW
    @0
    @18
    dochshpsat.h
    @23
    eqid
    #
    dochshpsat.o
    dochshpsat.k
    wph
    @8
    @10
    @0
    @23
    crn
    #
    wcel
    dochshpsat.k
    @13
    cU
    cH
    @23
    cK
    c.pe
    @9
    cW
    cX
    dochshpsat.h
    @24
    dochshpsat.u
    @12
    dochshpsat.o
    dochcl
    syl2anc
    wph
    @8
    @18
    @25
    wcel
    dochshpsat.k
    cU
    cH
    @23
    cK
    cW
    @17
    dochshpsat.h
    @24
    dochshpsat.u
    @20
    dih0rn
    syl
    doch11
    adantr
    bitr3d
    mtbird
    wph
    @16
    @2
    wb
    @3
    wph
    @15
    @1
    cX
    wph
    cU
    cH
    cK
    c.pe
    @9
    cW
    cX
    cY
    dochshpsat.h
    dochshpsat.o
    dochshpsat.u
    @12
    dochshpsat.y
    dochshpsat.k
    dochshpsat.x
    dochshpncl
    necon1bbid
    adantr
    mpbid
    impbida
end
