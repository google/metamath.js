include "wss.mm"
include "ssid.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "adantr.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "anbi2d.mm"
include "imbi12d.mm"
include "weq.mm"
include "wel.mm"
include "wn.mm"
include "simprl.mm"
include "simprr.mm"
include "unssad.mm"
include "jca.mm"
include "cdif.mm"
include "id.mm"
include "vsnid.mm"
include "elun2.mm"
include "mp1i.mm"
include "sseldd.mm"
include "ad2antll.mm"
include "simplr.mm"
include "eldifd.mm"
include "syl12anc.mm"
include "embantd.mm"
include "ex.mm"
include "com23.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpan2.mm"

theorem findcard2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume findcard2d.ch: |- ( x = (/) -> ( ps <-> ch ) )
  assume findcard2d.th: |- ( x = y -> ( ps <-> th ) )
  assume findcard2d.ta: |- ( x = ( y u. { z } ) -> ( ps <-> ta ) )
  assume findcard2d.et: |- ( x = A -> ( ps <-> et ) )
  assume findcard2d.z: |- ( ph -> ch )
  assume findcard2d.i: |- ( ( ph /\ ( y C_ A /\ z e. ( A \ y ) ) ) -> ( th -> ta ) )
  assume findcard2d.a: |- ( ph -> A e. Fin )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ps y
  disjoint ps z
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint et x
  assert |- ( ph -> et )

  proof
    wph
    cA
    cA
    wss
    #
    wet
    cA
    ssid
    cA
    cfn
    wcel
    #
    wph
    @0
    wa
    #
    wet
    wph
    @1
    @0
    findcard2d.a
    adantr
    wph
    vx
    cv
    #
    cA
    wss
    #
    wa
    #
    wps
    wi
    wph
    c0
    cA
    wss
    #
    wa
    #
    wch
    wi
    wph
    vy
    cv
    #
    cA
    wss
    #
    wa
    #
    wth
    wi
    #
    wph
    @8
    vz
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    wa
    #
    wta
    wi
    @2
    wet
    wi
    vx
    vy
    vz
    cA
    @3
    c0
    wceq
    #
    @5
    @7
    wps
    wch
    @17
    @4
    @6
    wph
    @3
    c0
    cA
    sseq1
    anbi2d
    findcard2d.ch
    imbi12d
    vx
    vy
    weq
    #
    @5
    @10
    wps
    wth
    @18
    @4
    @9
    wph
    @3
    @8
    cA
    sseq1
    anbi2d
    findcard2d.th
    imbi12d
    @3
    @14
    wceq
    #
    @5
    @16
    wps
    wta
    @19
    @4
    @15
    wph
    @3
    @14
    cA
    sseq1
    anbi2d
    findcard2d.ta
    imbi12d
    @3
    cA
    wceq
    #
    @5
    @2
    wps
    wet
    @20
    @4
    @0
    wph
    @3
    cA
    cA
    sseq1
    anbi2d
    findcard2d.et
    imbi12d
    wph
    wch
    @6
    findcard2d.z
    adantr
    @8
    cfn
    wcel
    #
    vz
    vy
    wel
    wn
    #
    wa
    #
    @16
    @11
    wta
    @23
    @16
    @11
    wta
    wi
    @23
    @16
    wa
    #
    @10
    wth
    wta
    @24
    wph
    @9
    @23
    wph
    @15
    simprl
    #
    @24
    @8
    @13
    cA
    @23
    wph
    @15
    simprr
    unssad
    #
    jca
    @24
    wph
    @9
    @12
    cA
    @8
    cdif
    wcel
    wth
    wta
    wi
    @25
    @26
    @24
    @12
    cA
    @8
    @15
    @12
    cA
    wcel
    @23
    wph
    @15
    @14
    cA
    @12
    @15
    id
    @12
    @13
    wcel
    @12
    @14
    wcel
    @15
    vz
    vsnid
    @12
    @13
    @8
    elun2
    mp1i
    sseldd
    ad2antll
    @21
    @22
    @16
    simplr
    eldifd
    findcard2d.i
    syl12anc
    embantd
    ex
    com23
    findcard2s
    mpcom
    mpan2
end
