include "aisbbisfaisf.mm"
include "aiffbbtat.mm"
include "dandysum2p2e4.mm"

theorem mdandysum2p2e4
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
  let wjth: wff jth
  let wjta: wff jta
  let vk: setvar k
  let vx: setvar x
  assume mdandysum2p2e4.1: |- ( jth <-> F. )
  assume mdandysum2p2e4.2: |- ( jta <-> T. )
  assume mdandysum2p2e4.a: |- ( ph <-> ( th /\ ta ) )
  assume mdandysum2p2e4.b: |- ( ps <-> ( et /\ ze ) )
  assume mdandysum2p2e4.c: |- ( ch <-> ( si /\ rh ) )
  assume mdandysum2p2e4.d: |- ( th <-> jth )
  assume mdandysum2p2e4.e: |- ( ta <-> jth )
  assume mdandysum2p2e4.f: |- ( et <-> jta )
  assume mdandysum2p2e4.g: |- ( ze <-> jta )
  assume mdandysum2p2e4.h: |- ( si <-> jth )
  assume mdandysum2p2e4.i: |- ( rh <-> jth )
  assume mdandysum2p2e4.j: |- ( mu <-> jth )
  assume mdandysum2p2e4.k: |- ( la <-> jth )
  assume mdandysum2p2e4.l: |- ( ka <-> ( ( th \/_ ta ) \/_ ( th /\ ta ) ) )
  assume mdandysum2p2e4.m: |- ( jph <-> ( ( et \/_ ze ) \/ ph ) )
  assume mdandysum2p2e4.n: |- ( jps <-> ( ( si \/_ rh ) \/ ps ) )
  assume mdandysum2p2e4.o: |- ( jch <-> ( ( mu \/_ la ) \/ ch ) )


  assert |- ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ph <-> ( th /\ ta ) ) /\ ( ps <-> ( et /\ ze ) ) ) /\ ( ch <-> ( si /\ rh ) ) ) /\ ( th <-> F. ) ) /\ ( ta <-> F. ) ) /\ ( et <-> T. ) ) /\ ( ze <-> T. ) ) /\ ( si <-> F. ) ) /\ ( rh <-> F. ) ) /\ ( mu <-> F. ) ) /\ ( la <-> F. ) ) /\ ( ka <-> ( ( th \/_ ta ) \/_ ( th /\ ta ) ) ) ) /\ ( jph <-> ( ( et \/_ ze ) \/ ph ) ) ) /\ ( jps <-> ( ( si \/_ rh ) \/ ps ) ) ) /\ ( jch <-> ( ( mu \/_ la ) \/ ch ) ) ) -> ( ( ( ( ka <-> F. ) /\ ( jph <-> F. ) ) /\ ( jps <-> T. ) ) /\ ( jch <-> F. ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wsi
    wrh
    wmu
    wla
    wka
    wjph
    wjps
    wjch
    mdandysum2p2e4.a
    mdandysum2p2e4.b
    mdandysum2p2e4.c
    wth
    wjth
    mdandysum2p2e4.d
    mdandysum2p2e4.1
    aisbbisfaisf
    wta
    wjth
    mdandysum2p2e4.e
    mdandysum2p2e4.1
    aisbbisfaisf
    wet
    wjta
    mdandysum2p2e4.f
    mdandysum2p2e4.2
    aiffbbtat
    wze
    wjta
    mdandysum2p2e4.g
    mdandysum2p2e4.2
    aiffbbtat
    wsi
    wjth
    mdandysum2p2e4.h
    mdandysum2p2e4.1
    aisbbisfaisf
    wrh
    wjth
    mdandysum2p2e4.i
    mdandysum2p2e4.1
    aisbbisfaisf
    wmu
    wjth
    mdandysum2p2e4.j
    mdandysum2p2e4.1
    aisbbisfaisf
    wla
    wjth
    mdandysum2p2e4.k
    mdandysum2p2e4.1
    aisbbisfaisf
    mdandysum2p2e4.l
    mdandysum2p2e4.m
    mdandysum2p2e4.n
    mdandysum2p2e4.o
    dandysum2p2e4
end
