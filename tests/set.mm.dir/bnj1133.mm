include "cv.mm"
include "cep.mm"
include "wfr.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wfn.mm"
include "bnj1071.mm"
include "bnj769.mm"
include "wal.mm"
include "wa.mm"
include "impexp.mm"
include "bicomi.mm"
include "albii.mm"
include "mpgbir.mm"
include "df-ral.mm"
include "mpbir.mm"
include "vex.mm"
include "bnj110.mm"
include "sylancl.mm"

theorem bnj1133
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let cD: class D
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  assume bnj1133.3: |- D = ( _om \ { (/) } )
  assume bnj1133.5: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1133.7: |- ( ta <-> A. j e. n ( j _E i -> [. j / i ]. th ) )
  assume bnj1133.8: |- ( ( i e. n /\ ta ) -> th )

  disjoint i j
  disjoint i n
  disjoint j n
  disjoint j th
  assert |- ( ch -> A. i e. n th )

  proof
    wch
    vn
    cv
    #
    cep
    wfr
    #
    wta
    wth
    wi
    #
    vi
    @0
    wral
    #
    wth
    vi
    @0
    wral
    @0
    cD
    wcel
    vf
    cv
    @0
    wfn
    wph
    wps
    @1
    wch
    bnj1133.5
    cD
    vn
    bnj1133.3
    bnj1071
    bnj769
    @3
    vi
    cv
    @0
    wcel
    #
    @2
    wi
    #
    vi
    wal
    #
    @6
    @4
    wta
    wa
    wth
    wi
    #
    vi
    @5
    @7
    vi
    @7
    @5
    @4
    wta
    wth
    impexp
    bicomi
    albii
    bnj1133.8
    mpgbir
    @2
    vi
    @0
    df-ral
    mpbir
    wth
    wta
    vi
    vj
    @0
    cep
    vn
    vex
    bnj1133.7
    bnj110
    sylancl
end
