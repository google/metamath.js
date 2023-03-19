include "cv.mm"
include "clsa.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "wrex.mm"
include "eqid.mm"
include "dvh1dimat.mm"
include "wa.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "adantr.mm"
include "simpr.mm"
include "lsateln0.mm"
include "wel.mm"
include "lsatssv.mm"
include "sseld.mm"
include "anim1d.mm"
include "reximdv2.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem dvh1dim
  let wph: wff ph
  let vz: setvar z
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vp: setvar p
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dvh3dim.h: |- H = ( LHyp ` K )
  assume dvh3dim.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh3dim.v: |- V = ( Base ` U )
  assume dvh1dim.o: |- .0. = ( 0g ` U )
  assume dvh1dim.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint .0. z
  disjoint U z
  disjoint V z
  disjoint ph z
  disjoint K p
  disjoint p z
  disjoint N p
  disjoint N z
  disjoint .0. p
  disjoint U p
  disjoint V p
  disjoint W p
  disjoint X p
  disjoint X z
  disjoint Y p
  disjoint Y z
  disjoint Z p
  disjoint Z z
  disjoint p ph
  assert |- ( ph -> E. z e. V z =/= .0. )

  proof
    wph
    vp
    cv
    #
    cU
    clsa
    cfv
    #
    wcel
    #
    vz
    cv
    #
    c.0
    wne
    #
    vz
    cV
    wrex
    #
    vp
    wph
    @1
    cU
    cH
    cK
    cW
    vp
    dvh3dim.h
    dvh3dim.u
    @1
    eqid
    #
    dvh1dim.k
    dvh1dimat
    wph
    @2
    wa
    #
    @4
    vz
    @0
    wrex
    @5
    @7
    vz
    @1
    @0
    cU
    c.0
    dvh1dim.o
    @6
    wph
    cU
    clmod
    wcel
    @2
    wph
    cU
    cH
    cK
    cW
    dvh3dim.h
    dvh3dim.u
    dvh1dim.k
    dvhlmod
    adantr
    #
    wph
    @2
    simpr
    #
    lsateln0
    @7
    @4
    @4
    vz
    @0
    cV
    @7
    vz
    vp
    wel
    @3
    cV
    wcel
    @4
    @7
    @0
    cV
    @3
    @7
    @1
    @0
    cV
    cU
    dvh3dim.v
    @6
    @8
    @9
    lsatssv
    sseld
    anim1d
    reximdv2
    mpd
    exlimddv
end
