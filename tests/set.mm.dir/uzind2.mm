include "cz.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "zltp1le.mm"
include "wi.mm"
include "peano2z.mm"
include "cv.mm"
include "wceq.mm"
include "imbi2d.mm"
include "a1i.mm"
include "w3a.mm"
include "3expia.mm"
include "sylbird.mm"
include "ex.mm"
include "com3l.mm"
include "imp.mm"
include "3adant1.mm"
include "a2d.mm"
include "uzind.mm"
include "3exp.mm"
include "syl.mm"
include "com34.mm"
include "pm2.43a.mm"
include "sylbid.mm"
include "3impia.mm"

theorem uzind2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume uzind2.1: |- ( j = ( M + 1 ) -> ( ph <-> ps ) )
  assume uzind2.2: |- ( j = k -> ( ph <-> ch ) )
  assume uzind2.3: |- ( j = ( k + 1 ) -> ( ph <-> th ) )
  assume uzind2.4: |- ( j = N -> ( ph <-> ta ) )
  assume uzind2.5: |- ( M e. ZZ -> ps )
  assume uzind2.6: |- ( ( M e. ZZ /\ k e. ZZ /\ M < k ) -> ( ch -> th ) )

  disjoint N j
  disjoint j ps
  disjoint ch j
  disjoint j th
  disjoint j ta
  disjoint k ph
  disjoint j k
  disjoint M j
  disjoint M k
  assert |- ( ( M e. ZZ /\ N e. ZZ /\ M < N ) -> ta )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    clt
    wbr
    #
    wta
    @0
    @1
    wa
    @2
    cM
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    wta
    cM
    cN
    zltp1le
    @0
    @1
    @4
    wta
    wi
    #
    @1
    @0
    @5
    @0
    @1
    @4
    @0
    wta
    @0
    @3
    cz
    wcel
    #
    @1
    @4
    @0
    wta
    wi
    #
    wi
    wi
    cM
    peano2z
    @6
    @1
    @4
    @7
    @0
    wph
    wi
    @0
    wps
    wi
    #
    @0
    wch
    wi
    @0
    wth
    wi
    @7
    vj
    vk
    @3
    cN
    vj
    cv
    #
    @3
    wceq
    wph
    wps
    @0
    uzind2.1
    imbi2d
    @9
    vk
    cv
    #
    wceq
    wph
    wch
    @0
    uzind2.2
    imbi2d
    @9
    @10
    c1
    caddc
    co
    wceq
    wph
    wth
    @0
    uzind2.3
    imbi2d
    @9
    cN
    wceq
    wph
    wta
    @0
    uzind2.4
    imbi2d
    @8
    @6
    uzind2.5
    a1i
    @6
    @10
    cz
    wcel
    #
    @3
    @10
    cle
    wbr
    #
    w3a
    @0
    wch
    wth
    @11
    @12
    @0
    wch
    wth
    wi
    #
    wi
    #
    @6
    @11
    @12
    @14
    @0
    @11
    @12
    @13
    @0
    @11
    @12
    @13
    wi
    @0
    @11
    wa
    @12
    cM
    @10
    clt
    wbr
    #
    @13
    cM
    @10
    zltp1le
    @0
    @11
    @15
    @13
    uzind2.6
    3expia
    sylbird
    ex
    com3l
    imp
    3adant1
    a2d
    uzind
    3exp
    syl
    com34
    pm2.43a
    imp
    sylbid
    3impia
end
