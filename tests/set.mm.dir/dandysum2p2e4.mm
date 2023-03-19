include "wfal.mm"
include "wb.mm"
include "wa.mm"
include "wtru.mm"
include "wxo.mm"
include "wo.mm"
include "biimpi.mm"
include "bothfbothsame.mm"
include "aisbnaxb.mm"
include "aisfina.mm"
include "notatnand.mm"
include "2false.mm"
include "aibnbaif.mm"
include "bothtbothsame.mm"
include "mtbir.mm"
include "pm3.2ni.mm"
include "pm3.2i.mm"
include "astbstanbst.mm"
include "aiffbbtat.mm"
include "aistia.mm"
include "olci.mm"
include "bitru.mm"
include "a1i.mm"

theorem dandysum2p2e4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let wmu: wff mu
  let wla: wff la
  let wka: wff ka
  let wjph: wff jph
  let wjps: wff jps
  let wjch: wff jch
  let vk: setvar k
  let vx: setvar x
  assume dandysum2p2e4.a: |- ( ph <-> ( th /\ ta ) )
  assume dandysum2p2e4.b: |- ( ps <-> ( et /\ ze ) )
  assume dandysum2p2e4.c: |- ( ch <-> ( si /\ rh ) )
  assume dandysum2p2e4.d: |- ( th <-> F. )
  assume dandysum2p2e4.e: |- ( ta <-> F. )
  assume dandysum2p2e4.f: |- ( et <-> T. )
  assume dandysum2p2e4.g: |- ( ze <-> T. )
  assume dandysum2p2e4.h: |- ( si <-> F. )
  assume dandysum2p2e4.i: |- ( rh <-> F. )
  assume dandysum2p2e4.j: |- ( mu <-> F. )
  assume dandysum2p2e4.k: |- ( la <-> F. )
  assume dandysum2p2e4.l: |- ( ka <-> ( ( th \/_ ta ) \/_ ( th /\ ta ) ) )
  assume dandysum2p2e4.m: |- ( jph <-> ( ( et \/_ ze ) \/ ph ) )
  assume dandysum2p2e4.n: |- ( jps <-> ( ( si \/_ rh ) \/ ps ) )
  assume dandysum2p2e4.o: |- ( jch <-> ( ( mu \/_ la ) \/ ch ) )


  assert |- ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ph <-> ( th /\ ta ) ) /\ ( ps <-> ( et /\ ze ) ) ) /\ ( ch <-> ( si /\ rh ) ) ) /\ ( th <-> F. ) ) /\ ( ta <-> F. ) ) /\ ( et <-> T. ) ) /\ ( ze <-> T. ) ) /\ ( si <-> F. ) ) /\ ( rh <-> F. ) ) /\ ( mu <-> F. ) ) /\ ( la <-> F. ) ) /\ ( ka <-> ( ( th \/_ ta ) \/_ ( th /\ ta ) ) ) ) /\ ( jph <-> ( ( et \/_ ze ) \/ ph ) ) ) /\ ( jps <-> ( ( si \/_ rh ) \/ ps ) ) ) /\ ( jch <-> ( ( mu \/_ la ) \/ ch ) ) ) -> ( ( ( ( ka <-> F. ) /\ ( jph <-> F. ) ) /\ ( jps <-> T. ) ) /\ ( jch <-> F. ) ) )

  proof
    wka
    wfal
    wb
    #
    wjph
    wfal
    wb
    #
    wa
    #
    wjps
    wtru
    wb
    #
    wa
    #
    wjch
    wfal
    wb
    #
    wa
    wph
    wth
    wta
    wa
    #
    wb
    wps
    wet
    wze
    wa
    #
    wb
    wa
    wch
    wsi
    wrh
    wa
    #
    wb
    wa
    wth
    wfal
    wb
    wa
    wta
    wfal
    wb
    wa
    wet
    wtru
    wb
    wa
    wze
    wtru
    wb
    wa
    wsi
    wfal
    wb
    wa
    wrh
    wfal
    wb
    wa
    wmu
    wfal
    wb
    wa
    wla
    wfal
    wb
    wa
    wka
    wth
    wta
    wxo
    #
    @6
    wxo
    #
    wb
    wa
    wjph
    wet
    wze
    wxo
    #
    wph
    wo
    #
    wb
    wa
    wjps
    wsi
    wrh
    wxo
    #
    wps
    wo
    #
    wb
    wa
    wjch
    wmu
    wla
    wxo
    #
    wch
    wo
    #
    wb
    wa
    @4
    @5
    @2
    @3
    @0
    @1
    wka
    @10
    wka
    @10
    dandysum2p2e4.l
    biimpi
    @9
    @6
    @9
    @6
    wth
    wta
    wth
    wta
    dandysum2p2e4.d
    dandysum2p2e4.e
    bothfbothsame
    aisbnaxb
    wth
    wta
    wth
    dandysum2p2e4.d
    aisfina
    notatnand
    #
    2false
    aisbnaxb
    aibnbaif
    wjph
    @12
    wjph
    @12
    dandysum2p2e4.m
    biimpi
    @11
    wph
    wet
    wze
    wet
    wze
    dandysum2p2e4.f
    dandysum2p2e4.g
    bothtbothsame
    aisbnaxb
    wph
    @6
    @17
    dandysum2p2e4.a
    mtbir
    pm3.2ni
    aibnbaif
    pm3.2i
    wjps
    @14
    dandysum2p2e4.n
    @14
    wps
    @13
    wps
    wps
    @7
    dandysum2p2e4.b
    wet
    wze
    dandysum2p2e4.f
    dandysum2p2e4.g
    astbstanbst
    aiffbbtat
    aistia
    olci
    bitru
    aiffbbtat
    pm3.2i
    wjch
    @16
    wjch
    @16
    dandysum2p2e4.o
    biimpi
    @15
    wch
    wmu
    wla
    wmu
    wla
    dandysum2p2e4.j
    dandysum2p2e4.k
    bothfbothsame
    aisbnaxb
    wch
    @8
    wsi
    wrh
    wsi
    dandysum2p2e4.h
    aisfina
    notatnand
    dandysum2p2e4.c
    mtbir
    pm3.2ni
    aibnbaif
    pm3.2i
    a1i
end
