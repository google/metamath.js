include "cv.mm"
include "wss.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wcel.mm"
include "wceq.mm"
include "anbi12d.mm"
include "wi.mm"
include "wal.mm"
include "id.mm"
include "unssad.mm"
include "adantr.mm"
include "a1i.mm"
include "alrimiv.mm"
include "ssintab.mm"
include "sylibr.mm"
include "jca.mm"
include "clublem.mm"
include "simpl.mm"
include "dmss.mm"
include "rnss.mm"
include "unss12.mm"
include "ssres2.mm"
include "3syl.mm"
include "simprr.mm"
include "sstrd.mm"
include "unss.mm"
include "syl6ib.mm"
include "eqssd.mm"
include "mpteq2ia.mm"

theorem mptrcllem
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  assume mptrcllem.ex1: |- ( x e. V -> |^| { y | ( x C_ y /\ ( ph /\ ( _I |` ( dom y u. ran y ) ) C_ y ) ) } e. _V )
  assume mptrcllem.ex2: |- ( x e. V -> |^| { z | ( ( x u. ( _I |` ( dom x u. ran x ) ) ) C_ z /\ ps ) } e. _V )
  assume mptrcllem.hyp1: |- ( x e. V -> ch )
  assume mptrcllem.hyp2: |- ( x e. V -> th )
  assume mptrcllem.hyp3: |- ( x e. V -> ta )
  assume mptrcllem.sub1: |- ( y = |^| { z | ( ( x u. ( _I |` ( dom x u. ran x ) ) ) C_ z /\ ps ) } -> ( ph <-> ch ) )
  assume mptrcllem.sub2: |- ( y = |^| { z | ( ( x u. ( _I |` ( dom x u. ran x ) ) ) C_ z /\ ps ) } -> ( ( _I |` ( dom y u. ran y ) ) C_ y <-> th ) )
  assume mptrcllem.sub3: |- ( z = |^| { y | ( x C_ y /\ ( ph /\ ( _I |` ( dom y u. ran y ) ) C_ y ) ) } -> ( ps <-> ta ) )

  disjoint x y
  disjoint x z
  disjoint V x
  disjoint y z
  disjoint V y
  disjoint V z
  disjoint ph x
  disjoint ph z
  disjoint ps x
  disjoint ps y
  disjoint ch y
  disjoint th y
  disjoint ta z
  assert |- ( x e. V |-> |^| { y | ( x C_ y /\ ( ph /\ ( _I |` ( dom y u. ran y ) ) C_ y ) ) } ) = ( x e. V |-> |^| { z | ( ( x u. ( _I |` ( dom x u. ran x ) ) ) C_ z /\ ps ) } )

  proof
    vx
    cV
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    wph
    cid
    @1
    cdm
    #
    @1
    crn
    #
    cun
    #
    cres
    #
    @1
    wss
    #
    wa
    #
    wa
    #
    vy
    cab
    cint
    #
    @0
    cid
    @0
    cdm
    #
    @0
    crn
    #
    cun
    #
    cres
    #
    cun
    #
    vz
    cv
    #
    wss
    #
    wps
    wa
    #
    vz
    cab
    cint
    #
    @0
    cV
    wcel
    #
    @10
    @19
    @20
    @8
    wch
    wth
    wa
    vy
    @0
    @19
    mptrcllem.ex2
    @1
    @19
    wceq
    wph
    wch
    @7
    wth
    mptrcllem.sub1
    mptrcllem.sub2
    anbi12d
    @20
    @18
    @0
    @16
    wss
    #
    wi
    #
    vz
    wal
    @0
    @19
    wss
    @20
    @22
    vz
    @22
    @20
    @17
    @21
    wps
    @17
    @0
    @14
    @16
    @17
    id
    unssad
    adantr
    a1i
    alrimiv
    @18
    vz
    @0
    ssintab
    sylibr
    @20
    wch
    wth
    mptrcllem.hyp1
    mptrcllem.hyp2
    jca
    clublem
    @20
    wps
    wta
    vz
    @15
    @10
    mptrcllem.ex1
    mptrcllem.sub3
    @20
    @9
    @15
    @1
    wss
    #
    wi
    #
    vy
    wal
    @15
    @10
    wss
    @20
    @24
    vy
    @20
    @9
    @2
    @14
    @1
    wss
    #
    wa
    #
    @23
    @9
    @26
    wi
    @20
    @9
    @2
    @25
    @2
    @8
    simpl
    @9
    @14
    @6
    @1
    @2
    @14
    @6
    wss
    #
    @8
    @2
    @11
    @3
    wss
    #
    @12
    @4
    wss
    #
    wa
    @13
    @5
    wss
    @27
    @2
    @28
    @29
    @0
    @1
    dmss
    @0
    @1
    rnss
    jca
    @11
    @3
    @12
    @4
    unss12
    @13
    @5
    cid
    ssres2
    3syl
    adantr
    @2
    wph
    @7
    simprr
    sstrd
    jca
    a1i
    @0
    @14
    @1
    unss
    syl6ib
    alrimiv
    @9
    vy
    @15
    ssintab
    sylibr
    mptrcllem.hyp3
    clublem
    eqssd
    mpteq2ia
end
